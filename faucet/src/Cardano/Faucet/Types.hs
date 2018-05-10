{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DuplicateRecordFields      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE TemplateHaskell            #-}
module Cardano.Faucet.Types (
   Config(..), mkConfig
 , HasConfig(..)
 , WithDrawlRequest(..), wWalletId, wAmount
 , WithDrawlResult(..)
 , DepositRequest(..), dWalletId, dAmount
 , DepositResult(..)
 , M, runM

  ) where

import           Control.Lens hiding ((.=))
import           Control.Lens.TH
import           Control.Monad.Reader
import           Data.Aeson (FromJSON (..), ToJSON (..), object, withObject, (.:), (.=))
import           Data.Typeable (Typeable)
import           GHC.Generics (Generic)
import           Servant (Handler)

--------------------------------------------------------------------------------
data WithDrawlRequest = WithDrawlRequest {
    _wWalletId :: String -- Pos.Wallet.Web.ClientTypes.Types.CAccountId
  , _wAmount   :: Double -- Pos.Core.Common.Types.Coin
  } deriving (Show, Typeable, Generic)

makeLenses ''WithDrawlRequest

instance FromJSON WithDrawlRequest where
  parseJSON = withObject "WithDrawlRequest" $ \v -> WithDrawlRequest
    <$> v .: "wallet"
    <*> v .: "amount"

instance ToJSON WithDrawlRequest where
    toJSON (WithDrawlRequest w a) =
        object ["wallet" .= w, "amount" .= a]

data WithDrawlResult = WithDrawlResult
  deriving (Show, Typeable, Generic)

instance ToJSON WithDrawlResult


--------------------------------------------------------------------------------
data DepositRequest = DepositRequest {
    _dWalletId :: String
  , _dAmount   :: Double
  } deriving (Show, Typeable, Generic)

makeLenses ''DepositRequest

instance FromJSON DepositRequest where
  parseJSON = withObject "DepositRequest" $ \v -> DepositRequest
    <$> v .: "wallet"
    <*> v .: "amount"

data DepositResult = DepositResult
  deriving (Show, Typeable, Generic)

instance ToJSON DepositResult

--------------------------------------------------------------------------------
data Config = Config {
    _walletApiURL :: String
  }

makeClassy ''Config

mkConfig :: String -> Config
mkConfig = Config

--------------------------------------------------------------------------------
newtype M a = M { unM :: ReaderT Config Handler a }
  deriving (Functor, Applicative, Monad, MonadReader Config, MonadIO)

runM :: Config -> M a -> Handler a
runM c = flip runReaderT c . unM
