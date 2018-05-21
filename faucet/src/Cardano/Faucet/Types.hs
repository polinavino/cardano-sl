{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DuplicateRecordFields      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE ViewPatterns               #-}
{-# OPTIONS_GHC -Wall #-}
module Cardano.Faucet.Types (
   FaucetConfig(..), mkFaucetConfig, testFC
 , HasFaucetConfig(..)
 , FaucetEnv(..), initEnv
 , HasFaucetEnv(..)
 , incWithDrawn
 , decrWithDrawn
 , setWalletBalance
 , WithDrawlRequest(..), wAddress, wAmount
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
import qualified Data.ByteString as BS
import           Data.Default (def)
import           Data.Monoid ((<>))
import           Data.Text (Text)
import           Data.Text.Lens (packed)
import           Data.Typeable (Typeable)
import           GHC.Generics (Generic)
import           Network.Connection (TLSSettings (..))
import           Network.HTTP.Client (Manager, newManager)
import           Network.HTTP.Client.TLS (mkManagerSettings)
import           Network.TLS (ClientParams (..), credentialLoadX509FromMemory, defaultParamsClient,
                              onCertificateRequest, onServerCertificate, supportedCiphers)
import           Network.TLS.Extra.Cipher (ciphersuite_all)
import           Servant (ServantErr)
import           Servant.Client.Core (BaseUrl (..), Scheme (..))
import           System.Metrics (Store, createCounter, createGauge)
import           System.Metrics.Counter (Counter)
import qualified System.Metrics.Counter as Counter
import           System.Metrics.Gauge (Gauge)
import qualified System.Metrics.Gauge as Gauge
import           System.Remote.Monitoring.Statsd (StatsdOptions, defaultStatsdOptions)
import           System.Wlog (CanLog, HasLoggerName, LoggerName (..), LoggerNameBox (..),
                              WithLogger, launchFromFile)

import           Cardano.Wallet.API.V1.Types (PaymentSource (..), Transaction,
                                              V1, WalletId (..))
import           Cardano.Wallet.Client (ClientError (..), WalletClient)
import           Cardano.Wallet.Client.Http (mkHttpClient)
import           Pos.Core (Address (..), Coin (..))
--

--------------------------------------------------------------------------------
data WithDrawlRequest = WithDrawlRequest {
    _wAddress :: V1 Address -- Pos.Wallet.Web.ClientTypes.Types.CAccountId
  , _wAmount  :: V1 Coin -- Pos.Core.Common.Types.Coin
  } deriving (Show, Typeable, Generic)

makeLenses ''WithDrawlRequest

instance FromJSON WithDrawlRequest where
  parseJSON = withObject "WithDrawlRequest" $ \v -> WithDrawlRequest
    <$> v .: "address"
    <*> v .: "amount"

instance ToJSON WithDrawlRequest where
    toJSON (WithDrawlRequest w a) =
        object ["address" .= w, "amount" .= a]

data WithDrawlResult =
    WithdrawlError ClientError
  | WithdrawlSuccess Transaction
  deriving (Show, Typeable, Generic)

instance ToJSON WithDrawlResult where
    toJSON (WithdrawlSuccess txn) =
        object ["success" .= txn]
    toJSON (WithdrawlError err) =
        object ["error" .= show err]


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
  , _fcPubCertFile         :: FilePath
  , _fcPrivKeyFile         :: FilePath
  }

makeClassy ''FaucetConfig

mkFaucetConfig
    :: String
    -> Int
    -> PaymentSource
    -> StatsdOptions
    -> FilePath
    -> FilePath
    -> FilePath
    -> FaucetConfig
mkFaucetConfig = FaucetConfig

testFC :: FaucetConfig
testFC = FaucetConfig "127.0.0.1" 8090 ps defaultStatsdOptions "./logging.cfg" "./tls/ca.crt" "./tls/server.key"
    where
        ps = PaymentSource (WalletId "Ae2tdPwUPEZLBG2sEmiv8Y6DqD4LoZKQ5wosXucbLnYoacg2YZSPhMn4ETi") 2147483648

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
    manager <- createManager fc
    let url = BaseUrl Https (fc ^. fcWalletApiHost) (fc ^. fcWalletApiPort) ""
    return $ FaucetEnv withdrawn withdrawCount balance
                       store
                       fc
                       (mkHttpClient url manager)

createManager :: FaucetConfig -> IO Manager
createManager fc = do
    pubCert <- BS.readFile (fc ^. fcPubCertFile)
    privKey <- BS.readFile (fc ^. fcPrivKeyFile)
    case credentialLoadX509FromMemory pubCert privKey of
        Left problem -> error $ "Unable to load credentials: " <> (problem ^. packed)
        Right credential ->
            let hooks = def {
                            onCertificateRequest = \_ -> return $ Just credential,
                            onServerCertificate  = \_ _ _ _ -> return []
                        }
                clientParams = (defaultParamsClient "localhost" "") {
                                   clientHooks = hooks,
                                   clientSupported = def {
                                       supportedCiphers = ciphersuite_all
                                   }
                               }
                tlsSettings = TLSSettings clientParams
            in
            newManager $ mkManagerSettings tlsSettings Nothing

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
