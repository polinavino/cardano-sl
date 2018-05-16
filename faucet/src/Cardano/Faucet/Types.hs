{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE ConstraintKinds #-}
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
 , MonadFaucet
  ) where

import           Control.Lens hiding ((.=))
import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.Aeson (FromJSON (..), ToJSON (..), object, withObject, (.:), (.=))
import Data.Text (Text)
import           Data.Typeable (Typeable)
import           GHC.Generics (Generic)
import           Servant (ServantErr)
import           Servant.Client.Core (BaseUrl (..), Scheme (..))
import           System.Metrics (Store, createCounter, createGauge)
import           System.Metrics.Counter (Counter)
import qualified System.Metrics.Counter as Counter
import           System.Metrics.Gauge (Gauge)
import qualified System.Metrics.Gauge as Gauge
import           System.Remote.Monitoring.Statsd (StatsdOptions)
import           System.Wlog (CanLog, WithLogger, HasLoggerName, LoggerName (..), LoggerNameBox (..),
                              launchFromFile)

import           Cardano.Wallet.API.V1.Types (PaymentSource (..))
import           Cardano.Wallet.Client (WalletClient)
import           Cardano.Wallet.Client.Http (defaultManagerSettings, mkHttpClient, newManager)
import           Pos.Core (Coin (..))
import           Pos.Wallet.Web.ClientTypes.Types (Addr (..), CAccountId (..), CId (..))

--------------------------------------------------------------------------------
data WithDrawlRequest = WithDrawlRequest {
    _wWalletId :: Text -- Pos.Wallet.Web.ClientTypes.Types.CAccountId
  , _wAmount   :: Coin -- Pos.Core.Common.Types.Coin
  } deriving (Show, Typeable, Generic)

makeLenses ''WithDrawlRequest

instance FromJSON WithDrawlRequest where
  parseJSON = withObject "WithDrawlRequest" $ \v -> WithDrawlRequest
    <$> v .: "wallet"
    <*> (Coin <$> v .: "amount")

instance ToJSON WithDrawlRequest where
    toJSON (WithDrawlRequest w (Coin a)) =
        object ["wallet" .= w, "amount" .= a]

data WithDrawlResult = WithDrawlResult
  deriving (Show, Typeable, Generic)

instance ToJSON WithDrawlResult


--------------------------------------------------------------------------------
data DepositRequest = DepositRequest {
    _dWalletId :: Text
  , _dAmount   :: Coin
  } deriving (Show, Typeable, Generic)

makeLenses ''DepositRequest

instance FromJSON DepositRequest where
  parseJSON = withObject "DepositRequest" $ \v -> DepositRequest
    <$> v .: "wallet"
    <*> (Coin <$> v .: "amount")

data DepositResult = DepositResult
  deriving (Show, Typeable, Generic)

instance ToJSON DepositResult

--------------------------------------------------------------------------------
data FaucetConfig = FaucetConfig {
    _fcWalletApiHost       :: String
  , _fcWalletApiPort       :: Int
  , _fcFaucetPaymentSource :: PaymentSource
  , _fcStatsdOpts          :: StatsdOptions
  , _fcLoggerConfigFile    :: FilePath
  }

makeClassy ''FaucetConfig

mkFaucetConfig :: String -> Int -> PaymentSource -> StatsdOptions -> String -> FaucetConfig
mkFaucetConfig = FaucetConfig

--------------------------------------------------------------------------------
data FaucetEnv = FaucetEnv {
    _feWithdrawn     :: Counter
  , _feNumWithdrawn  :: Counter
  , _feWalletBalance :: Gauge
  , _feStore         :: Store
  , _feFaucetConfig  :: FaucetConfig
  , _feWalletClient  :: WalletClient IO
  }

makeClassy ''FaucetEnv

--------------------------------------------------------------------------------
initEnv :: FaucetConfig -> Store -> IO FaucetEnv
initEnv fc store = do
    withdrawn <- createCounter "total-withdrawn" store
    withdrawCount <- createCounter "num-withdrawals" store
    balance <- createGauge "wallet-balance" store
    manager <- newManager defaultManagerSettings
    let url = BaseUrl Http (fc ^. fcWalletApiHost) (fc ^. fcWalletApiPort) ""
    return $ FaucetEnv withdrawn withdrawCount balance
                       store
                       fc
                       (mkHttpClient url manager)

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
newtype M a = M { unM :: ReaderT FaucetEnv (ExceptT ServantErr (LoggerNameBox IO)) a }
  deriving (Functor, Applicative, Monad, MonadReader FaucetEnv, CanLog, HasLoggerName, MonadIO)

runM :: FaucetEnv -> M a -> IO (Either ServantErr a)
runM c = launchFromFile (c ^. feFaucetConfig . fcLoggerConfigFile) (LoggerName "faucet")
       . runExceptT
       . flip runReaderT c
       . unM

type MonadFaucet c m = (MonadIO m, MonadReader c m, HasFaucetEnv c, WithLogger m, HasLoggerName m)
