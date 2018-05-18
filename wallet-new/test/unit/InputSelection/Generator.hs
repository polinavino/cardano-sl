{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module InputSelection.Generator (
    -- * Policy
    InputSelectionPolicy
    -- * Events
  , Event(..)
    -- * Interpreter
  , IntEvent
  , runIntEvent
  , runIntEvent_
  , intEvent
  ) where

import           Universum

import           Control.Lens ((%=), (.=))
import           Control.Lens.TH (makeLenses)
-- import           Test.QuickCheck

import           InputSelection.Policy
import           UTxO.DSL

{-------------------------------------------------------------------------------
  Events
-------------------------------------------------------------------------------}

data Event h a =
    Deposit (Utxo h a)
  | Pay [Output a]
  | NextSlot

{-------------------------------------------------------------------------------
  Abstraction over UTxO
-------------------------------------------------------------------------------}

class UtxoSet (utxo :: (* -> *) -> * -> *) where
  union :: Hash h a => Utxo h a -> utxo h a -> utxo h a
  removeInputs :: Hash h a => Set (Input h a) -> utxo h a -> utxo h a

instance UtxoSet Utxo where
  union = utxoUnion
  removeInputs = utxoRemoveInputs

{-------------------------------------------------------------------------------
  Interpreter monad
-------------------------------------------------------------------------------}

data IntParams utxo h a m = IntParams {
      intParamsPolicy :: InputSelectionPolicy utxo h a m
    }

data IntState utxo h a = IntState {
      _intStateUtxo :: utxo h a
    , _intStatePending :: Utxo h a
    , _intStateStats :: IntStats
    }

type IntStats = ()

makeLenses ''IntState

initStats :: IntStats
initStats = ()

initState :: utxo h a -> IntState utxo h a
initState utxo = IntState {
      _intStateUtxo    = utxo
    , _intStatePending = utxoEmpty
    , _intStateStats   = initStats
    }

newtype IntEvent utxo h a m x = Int {
    unInt :: ReaderT (IntParams utxo h a m) (StateT (IntState utxo h a) m) x
  }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadState (IntState utxo h a)
           , MonadReader (IntParams utxo h a m)
           )

instance MonadTrans (IntEvent utxo h a) where
  lift = Int . lift . lift

runIntEvent :: Monad m
            => IntParams utxo h a m
            -> utxo h a
            -> IntEvent utxo h a m x
            -> m (x, IntStats)
runIntEvent params utxo act =
    second (view intStateStats) <$>
      runStateT (runReaderT (unInt act) params) (initState utxo)

runIntEvent_ :: Monad m
             => IntParams utxo h a m
             -> utxo h a
             -> IntEvent utxo h a m x
             -> m IntStats
runIntEvent_ params utxo = fmap snd . runIntEvent params utxo

{-------------------------------------------------------------------------------
  Interpreter proper
-------------------------------------------------------------------------------}

intEvent :: forall m utxo h a. (Monad m, UtxoSet utxo, Hash h a)
         => Event h a -> IntEvent utxo h a m ()
intEvent = go
  where
    go :: Event h a -> IntEvent utxo h a m ()
    go (Deposit new) = intStateUtxo %= union new
    go (Pay outs)    = pay outs
    go NextSlot      = do pending <- use intStatePending
                          intStateUtxo    %= union pending
                          intStatePending .= utxoEmpty

pay :: (Monad m, UtxoSet utxo, Hash h a)
    => [Output a] -> IntEvent utxo h a m ()
pay outs = do
    IntParams{..} <- ask
    utxo <- use intStateUtxo
    mtx  <- lift $ intParamsPolicy utxo outs
    case mtx of
      Just tx -> do
        intStateUtxo    %= removeInputs (trIns tx)
        intStatePending %= utxoUnion (trUtxo tx)
      Nothing ->
        -- TODO: record some stats
        return ()

{-

input selection
coin selection

bitcoinj coin selection? ("multiple classes" -- multiple policies)

https://github.com/bitcoin/bitcoin/issues/7664

See ApproximateBestSubset in wallet.cpp.

sweep?



-}


{-
http://murch.one/wp-content/uploads/2016/11/erhardt2016coinselection.pdf
"An Evaluation of Coin Selection Strategies", Master’s Thesis, Mark Erhardt

2.3.4
A transaction output is labeled as dust when its value is similar to the cost of
spending it.Precisely, Bitcoin Core sets the dust limit to a value where spending an
2.3. Transactions 7
output would exceed 1/3 of its value. T

https://youtu.be/vnHQwYxB08Y?t=39m


https://www.youtube.com/watch?v=IKSSWUBqMCM

companies; hundreds of entries in UTxO
individuals: tens of entries

batch payments!
  (Harding, BitcoinTechTalk -- safe up to 80% of transaction fees)

coin selection --
  relatively minor importance
    batching, better representation (SegWit), .. much larger impact
    coin selection only a few percent savings

* FIFO is actually a reasonable strategy (!)
* So is random
    self correcting -- if you have a large amount of small inputs,
    they'll be more likely to be picked!
    (i.e, if 90% of the wallet is small inputs, 90% change of picking them!)

Branch&Bound seems to do exhaustive search (backtracking algorithm) to find
exact matches, coupled with random selection.

A Traceability Analysis of Monero’s Blockchain
https://eprint.iacr.org/2017/338.pdf
-}
