{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TemplateHaskell       #-}
module Cardano.Faucet.Types where

import           Control.Lens hiding ((.=))
import           Control.Lens.TH
import           Control.Monad.Reader
import           Data.Aeson (FromJSON (..), ToJSON (..), object, withObject, (.:), (.=))
import           Data.Typeable (Typeable)
import           GHC.Generics (Generic)

--------------------------------------------------------------------------------
data WithDrawlRequest = WithDrawlRequest {
    _wWalletId :: String
  , _wAmount   :: Double
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

newtype M m a = M { unM :: ReaderT Config m a }
