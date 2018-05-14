{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DuplicateRecordFields      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE ViewPatterns               #-}
{-# OPTIONS_GHC -Wall #-}
module Cardano.Faucet.Types (
   FaucetConfig(..), mkFaucetConfig
 , HasFaucetConfig(..)
 , FaucetEnv(..), initEnv
 , HasFaucetEnv(..)
 , incWithDrawn
 , decrWithDrawn
 , setWalletBalance
 , WithDrawlRequest(..), wWalletId, wAmount
 , WithDrawlResult(..)
 , DepositRequest(..), dWalletId, dAmount
 , DepositResult(..)
 , M, runM
  ) where

import           Control.Lens hiding ((.=))
import           Control.Monad.Reader
import           Data.Aeson (FromJSON (..), ToJSON (..), object, withObject, (.:), (.=))
import           Data.Typeable (Typeable)
import           GHC.Generics (Generic)
import           Servant (Handler)
import           System.Metrics (Store, createCounter, createGauge)
import           System.Metrics.Counter (Counter)
import qualified System.Metrics.Counter as Counter
import           System.Metrics.Gauge (Gauge)
import qualified System.Metrics.Gauge as Gauge
import           System.Remote.Monitoring.Statsd (StatsdOptions)

import           Pos.Core (Coin (..))
import           Pos.Wallet.Web.ClientTypes.Types (Addr (..), CAccountId (..), CId (..))

--------------------------------------------------------------------------------
data WithDrawlRequest = WithDrawlRequest {
    _wWalletId :: CAccountId -- Pos.Wallet.Web.ClientTypes.Types.CAccountId
  , _wAmount   :: Coin -- Pos.Core.Common.Types.Coin
  } deriving (Show, Typeable, Generic)

makeLenses ''WithDrawlRequest

instance FromJSON WithDrawlRequest where
  parseJSON = withObject "WithDrawlRequest" $ \v -> WithDrawlRequest
    <$> (CAccountId <$> v .: "wallet")
    <*> (Coin <$> v .: "amount")

instance ToJSON WithDrawlRequest where
    toJSON (WithDrawlRequest (CAccountId w) (Coin a)) =
        object ["wallet" .= w, "amount" .= a]

data WithDrawlResult = WithDrawlResult
  deriving (Show, Typeable, Generic)

instance ToJSON WithDrawlResult


--------------------------------------------------------------------------------
data DepositRequest = DepositRequest {
    _dWalletId :: CAccountId
  , _dAmount   :: Coin
  } deriving (Show, Typeable, Generic)

makeLenses ''DepositRequest

instance FromJSON DepositRequest where
  parseJSON = withObject "DepositRequest" $ \v -> DepositRequest
    <$> (CAccountId <$> v .: "wallet")
    <*> (Coin <$> v .: "amount")

data DepositResult = DepositResult
  deriving (Show, Typeable, Generic)

instance ToJSON DepositResult

--------------------------------------------------------------------------------
data FaucetConfig = FaucetConfig {
    _fcWalletApiURL :: String
  , _fcFaucetWallet :: CAccountId
  , _fcStatsdOpts   :: StatsdOptions
  }

makeClassy ''FaucetConfig

mkFaucetConfig :: String -> CAccountId -> StatsdOptions -> FaucetConfig
mkFaucetConfig = FaucetConfig

--------------------------------------------------------------------------------
data FaucetEnv = FaucetEnv {
    _feWithdrawn     :: Counter
  , _feNumWithdrawn  :: Counter
  , _feWalletBalance :: Gauge
  , _feStore         :: Store
  , _feFaucetWallet  :: CAccountId
  , _feWalletApiURL  :: String
  }

makeClassy ''FaucetEnv

--------------------------------------------------------------------------------
initEnv :: FaucetConfig -> Store -> IO FaucetEnv
initEnv fc store = do
    withdrawn <- createCounter "total-withdrawn" store
    withdrawCount <- createCounter "num-withdrawals" store
    balance <- createGauge "wallet-balance" store
    return $ FaucetEnv withdrawn withdrawCount balance
                       store
                       (fc ^. fcFaucetWallet)
                       (fc ^. fcWalletApiURL)

incWithDrawn :: (MonadReader e m, HasFaucetEnv e, MonadIO m) => Coin -> m ()
incWithDrawn (Coin (fromIntegral -> c)) = do
  wd <- view feWithdrawn
  wc <- view feNumWithdrawn
  bal <- view feWalletBalance
  liftIO $ do
    Counter.add wd c
    Counter.inc wc
    Gauge.add bal c

decrWithDrawn :: (MonadReader e m, HasFaucetEnv e, MonadIO m) => Coin -> m ()
decrWithDrawn (Coin (fromIntegral -> c)) = do
  -- wd <- view feWithdrawn
  -- wc <- view feNumWithdrawn
  bal <- view feWalletBalance
  liftIO $ do
    -- Counter.subtract wd c
    -- Counter.inc wc
    Gauge.subtract bal c

setWalletBalance :: (MonadReader e m, HasFaucetEnv e, MonadIO m) => Coin -> m ()
setWalletBalance (Coin (fromIntegral -> c)) = do
  bal <- view feWalletBalance
  liftIO $ Gauge.set bal c

--------------------------------------------------------------------------------
newtype M a = M { unM :: ReaderT FaucetEnv Handler a }
  deriving (Functor, Applicative, Monad, MonadReader FaucetEnv, MonadIO)

runM :: FaucetEnv -> M a -> Handler a
runM c = flip runReaderT c . unM
