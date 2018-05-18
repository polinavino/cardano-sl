module InputSelection.Policy (
    InputSelectionPolicy
  , random
  ) where

import           Universum

import qualified Data.Map as Map
import qualified Data.Set as Set
import           Test.QuickCheck

import           UTxO.DSL

{-------------------------------------------------------------------------------
  Policy
-------------------------------------------------------------------------------}

type InputSelectionPolicy utxo h a m = utxo h a -> [Output a] -> m (Maybe (Transaction h a))

{-------------------------------------------------------------------------------
  Random
-------------------------------------------------------------------------------}

-- | Random input selection
--
-- Random input selection has the advantage that is it self correcting, in the
-- following sense: suppose that 90% of our UTxO consists of small outputs;
-- then random selection has a 90% change of choosing those small outputs.
--
-- For each output we add a change output that is between 0.5 and 2 times the
-- size of the output, making it hard to identify.
random :: forall h a. InputSelectionPolicy Utxo h a Gen
random utxo outs = do
    let utxoMap   = utxoToMap utxo
        available = Set.fromDistinctAscList [0 .. Map.size utxoMap - 1]
    go utxoMap available outs Set.empty
  where
    go :: Map (Input h a) (Output a)  -- Utxo
       -> Set Int                     -- Available indices
       -> [Output a]                  -- Outputs to to do
       -> Set (Input h a)             -- Inputs selected so far
       -> Gen (Maybe (Transaction h a))
    go utxo available acc [] = undefined -- todo




-- | Random input selection: core algorithm
--
-- Select random inputs until we reach a value in the given bounds.
-- If such a value cannot be found, return @Nothing@.
random' :: forall h a. Hash h a
        => Map (Input h a) (Output a)    -- ^ Utxo
        -> (Value, Value)                -- ^ Value bounds we're aiming for
        -> Set Int                       -- ^ Available indices
        -> Gen (Maybe (Set (Input h a))) -- ^ Picked values, if successful
random' utxo (lo, hi) = go Set.empty 0
  where
    go :: Set (Input h a)
       -> Value
       -> Set Int
       -> Gen (Maybe (Set (Input h a)))
    go acc accSum available
      | lo <= accSum && accSum <= hi = return $ Just acc
      | Set.null available           = return Nothing
      | otherwise                    = pickRandom
      where
        pickRandom :: Gen (Maybe (Set (Input h a)))
        pickRandom = do
            ixix <- choose (0, Set.size available - 1)
            let ix         = Set.elemAt   ixix available
                available' = Set.deleteAt ixix available
                (inp, out) = Map.elemAt ix utxo
                acc'    = Set.insert inp acc
                accSum'     = accSum + outVal out
            if accSum' <= hi -- should we pick this value?
              then go acc' accSum' available'
              else go acc  accSum  available'




{-
  where
    go :: Map (Input h a) (Output a)
       -> Map (Output a) (Value, Set (Input h a))
       -> Gen (Maybe (Transaction h a))
    go utxo selected =
        if Map.null utxo
          then undefined
          else do
            ix <- choose (0, Map.size utxo - 1)


-}
