{-# LANGUAGE ScopedTypeVariables #-}

-- | Workers responsible for Leaders and Richmen computation.

module Pos.Lrc.Worker
       ( lrcOnNewSlotWorker
       , lrcSingleShot
       , lrcSingleShotNoLock
       ) where

import           Universum

import           Control.Monad.Catch        (bracketOnError)
import           Control.Monad.STM          (retry)
import qualified Data.HashMap.Strict        as HM
import qualified Data.HashSet               as HS
import           Formatting                 (build, sformat, (%))
import           Mockable                   (forConcurrently)
import           Paths_cardano_sl           (version)
import           Serokell.Util.Exceptions   ()
import           System.Wlog                (logInfo, logWarning)

import           Pos.Binary.Communication   ()
import           Pos.Block.Logic.Internal   (applyBlocksUnsafe, rollbackBlocksUnsafe,
                                             withBlkSemaphore_)
import           Pos.Communication.Protocol (NodeId, OutSpecs, WorkerSpec,
                                             localOnNewSlotWorker)
import           Pos.Constants              (slotSecurityParam)
import           Pos.Core                   (Coin)
import           Pos.DB.Class               (MonadDBCore)
import qualified Pos.DB.DB                  as DB
import qualified Pos.DB.GState              as GS
import           Pos.Lrc.Consumer           (LrcConsumer (..))
import           Pos.Lrc.Consumers          (allLrcConsumers)
import           Pos.Lrc.Context            (LrcContext (lcLrcSync), LrcSyncData (..))
import           Pos.Lrc.DB                 (IssuersStakes, getLeaders, getSeed, putEpoch,
                                             putIssuersStakes, putLeaders, putSeed)
import           Pos.Lrc.Error              (LrcError (..))
import           Pos.Lrc.Fts                (followTheSatoshiM)
import           Pos.Lrc.Logic              (findAllRichmenMaybe)
import           Pos.Reporting              (reportMisbehaviourMasked)
import           Pos.Ssc.Class              (SscWorkersClass)
import           Pos.Ssc.Extra              (sscCalculateSeed)
import           Pos.Types                  (EpochIndex, EpochOrSlot (..),
                                             EpochOrSlot (..), HeaderHash, HeaderHash,
                                             SharedSeed, SlotId (..), StakeholderId,
                                             crucialSlot, epochIndexL, getEpochOrSlot,
                                             getEpochOrSlot)
import           Pos.Update.DB              (getConfirmedBVStates)
import           Pos.Update.Poll.Types      (BlockVersionState (..))
import           Pos.Util                   (logWarningWaitLinear, maybeThrow)
import           Pos.Util.Chrono            (NewestFirst (..), toOldestFirst)
import           Pos.Util.Context           (askContext)
import           Pos.WorkMode               (WorkMode)

lrcOnNewSlotWorker
    :: (SscWorkersClass ssc, WorkMode ssc m, MonadDBCore m)
    => m (Set NodeId)
    -> (WorkerSpec m, OutSpecs)
lrcOnNewSlotWorker getPeers = localOnNewSlotWorker getPeers True $ \SlotId {..} ->
    when (siSlot < slotSecurityParam) $
    (lrcSingleShot getPeers siEpoch `catch` reportError) `catch` onLrcError
  where
    reportError (SomeException e) = do
        reportMisbehaviourMasked getPeers version $ "Lrc worker failed with error: " <> show e
        throwM e
    onLrcError UnknownBlocksForLrc =
        logInfo
            "LRC worker can't do anything, because recent blocks aren't known"
    onLrcError e = throwM e

-- | Run leaders and richmen computation for given epoch. If stable
-- block for this epoch is not known, LrcError will be thrown.
lrcSingleShot
    :: (SscWorkersClass ssc, WorkMode ssc m, MonadDBCore m)
    => m (Set NodeId) -> EpochIndex -> m ()
lrcSingleShot getPeers epoch = lrcSingleShotImpl getPeers True epoch allLrcConsumers

-- | Same, but doesn't take lock on the semaphore.
lrcSingleShotNoLock
    :: (SscWorkersClass ssc, WorkMode ssc m, MonadDBCore m)
    => m (Set NodeId) -> EpochIndex -> m ()
lrcSingleShotNoLock getPeers epoch = lrcSingleShotImpl getPeers False epoch allLrcConsumers

lrcSingleShotImpl
    :: (WorkMode ssc m, MonadDBCore m)
    => m (Set NodeId) -> Bool -> EpochIndex -> [LrcConsumer m] -> m ()
lrcSingleShotImpl getPeers withSemaphore epoch consumers = do
    lock <- askContext @LrcContext lcLrcSync
    tryAcquireExclusiveLock epoch lock onAcquiredLock
  where
    onAcquiredLock = do
        (need, filteredConsumers) <-
            logWarningWaitLinear 5 "determining whether LRC is needed" $ do
                expectedRichmenComp <-
                    filterM (flip lcIfNeedCompute epoch) consumers
                needComputeLeaders <- isNothing <$> getLeaders epoch
                let needComputeRichmen = not . null $ expectedRichmenComp
                when needComputeLeaders $ logInfo "Need to compute leaders"
                when needComputeRichmen $ logInfo "Need to compute richmen"
                return $
                    ( needComputeLeaders || needComputeRichmen
                    , expectedRichmenComp)
        when need $ do
            logInfo "LRC is starting"
            if withSemaphore
                then withBlkSemaphore_ $ lrcDo getPeers epoch filteredConsumers
            -- we don't change/use it in lcdDo in fact
                else void . lrcDo getPeers epoch filteredConsumers =<< GS.getTip
            logInfo "LRC has finished"
        putEpoch epoch
        logInfo "LRC has updated LRC DB"

tryAcquireExclusiveLock
    :: (MonadMask m, MonadIO m)
    => EpochIndex -> TVar LrcSyncData -> m () -> m ()
tryAcquireExclusiveLock epoch lock action =
    bracketOnError acquireLock (flip whenJust releaseLock) doAction
  where
    acquireLock = atomically $ do
        sync <- readTVar lock
        if | not (lrcNotRunning sync) {- i.e. lrc is running -} -> retry
           | lastEpochWithLrc sync >= epoch -> pure Nothing
           | lastEpochWithLrc sync == epoch - 1 -> do
                 writeTVar lock (LrcSyncData False (lastEpochWithLrc sync))
                 pure (Just (lastEpochWithLrc sync))
           | otherwise -> throwM UnknownBlocksForLrc
    releaseLock e = atomically $ writeTVar lock (LrcSyncData True e)
    doAction Nothing = pass
    doAction _       = action >> releaseLock epoch

lrcDo
    :: forall ssc m.
       WorkMode ssc m
    => m (Set NodeId) -> EpochIndex -> [LrcConsumer m] -> HeaderHash -> m HeaderHash
lrcDo getPeers epoch consumers tip = tip <$ do
    blundsUpToGenesis <- DB.loadBlundsFromTipWhile @ssc upToGenesis
    -- If there are blocks from 'epoch' it means that we somehow accepted them
    -- before running LRC for 'epoch'. It's very bad.
    unless (null blundsUpToGenesis) $ throwM LrcAfterGenesis
    NewestFirst blundsList <- DB.loadBlundsFromTipWhile whileAfterCrucial
    case nonEmpty blundsList of
        Nothing -> throwM UnknownBlocksForLrc
        Just (NewestFirst -> blunds) ->
            withBlocksRolledBack blunds $ do
                issuersComputationDo epoch
                richmenComputationDo epoch consumers
                DB.sanityCheckDB
                seed <- sscCalculateSeed epoch >>= \case
                    Right s -> do
                        logInfo $ sformat
                            ("Calculated seed for epoch "%build%
                             " successfully") epoch
                        return s
                    Left err -> do
                        logWarning $ sformat
                            ("SSC couldn't compute seed: "%build) err
                        logWarning "Going to reuse seed for previous epoch"
                        getSeed (epoch - 1) >>=
                            maybeThrow (CanNotReuseSeedForLrc (epoch - 1))
                putSeed epoch seed
                leadersComputationDo epoch seed
  where
    applyBack blunds = applyBlocksUnsafe getPeers blunds Nothing
    upToGenesis b = b ^. epochIndexL >= epoch
    whileAfterCrucial b = getEpochOrSlot b > crucial
    crucial = EpochOrSlot $ Right $ crucialSlot epoch
    withBlocksRolledBack blunds =
        bracket_ (rollbackBlocksUnsafe getPeers blunds)
                 (applyBack (toOldestFirst blunds))

issuersComputationDo :: forall ssc m . WorkMode ssc m => EpochIndex -> m ()
issuersComputationDo epochId = do
    issuers <- unionHSs .
               map (bvsIssuersStable . snd) <$>
               getConfirmedBVStates
    issuersStakes <- foldM putIsStake mempty issuers
    putIssuersStakes epochId issuersStakes
  where
    unionHSs = foldl' (flip HS.union) mempty
    putIsStake :: IssuersStakes -> StakeholderId -> m IssuersStakes
    putIsStake hm id = GS.getEffectiveStake id >>= \case
        Nothing ->
           hm <$ (logWarning $ sformat ("Stake for issuer "%build% " not found") id)
        Just stake -> pure $ HM.insert id stake hm

leadersComputationDo :: WorkMode ssc m => EpochIndex -> SharedSeed -> m ()
leadersComputationDo epochId seed =
    unlessM (isJust <$> getLeaders epochId) $ do
        totalStake <- GS.getEffectiveTotalStake
        leaders <- GS.runBalanceIterator $ followTheSatoshiM seed totalStake
        putLeaders epochId leaders

richmenComputationDo
    :: forall ssc m.
       WorkMode ssc m
    => EpochIndex -> [LrcConsumer m] -> m ()
richmenComputationDo epochIdx consumers = unless (null consumers) $ do
    total <- GS.getEffectiveTotalStake
    consumersAndThds <-
        zip consumers <$> mapM (flip lcThreshold total) consumers
    let minThreshold :: Maybe Coin
        minThreshold = safeThreshold consumersAndThds (not . lcConsiderDelegated)
        minThresholdD :: Maybe Coin
        minThresholdD = safeThreshold consumersAndThds lcConsiderDelegated
    (richmen, richmenD) <- GS.runBalanceIterator
                               (findAllRichmenMaybe minThreshold minThresholdD)
    let callCallback (cons, thd) =
            if lcConsiderDelegated cons
            then lcComputedCallback cons epochIdx total
                   (HM.filter (>= thd) richmenD)
            else lcComputedCallback cons epochIdx total
                   (HM.filter (>= thd) richmen)
    void $ forConcurrently consumersAndThds callCallback
  where
    safeThreshold consumersAndThds f =
        safeMinimum $ map snd $ filter (f . fst) consumersAndThds
    safeMinimum a
        | null a = Nothing
        | otherwise = Just $ minimum a
