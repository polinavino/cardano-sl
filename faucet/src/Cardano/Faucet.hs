{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE ConstraintKinds #-}
{-# OPTIONS_GHC -Wall #-}
module Cardano.Faucet (
    server
  , serverAPI
  , module Cardano.Faucet.Types
  ) where

import           Control.Lens
import Data.Monoid ((<>))
import Data.Text.Lens
import           Control.Monad.IO.Class
import           Servant
import           System.Wlog (HasLoggerName, LoggerName (..), WithLogger, logError, logInfo,
                              withSublogger)

import           Cardano.Faucet.Types
-- import           Client.Cardano.Wallet.Web.Run     (runEndpointClient)

type API = "withdraw" :> ReqBody '[JSON] WithDrawlRequest :> Post '[JSON] WithDrawlResult
      :<|> "deposit" :> ReqBody '[JSON] DepositRequest :> Post '[JSON] DepositResult

withdraw :: (MonadFaucet c m) => WithDrawlRequest -> m WithDrawlResult
withdraw wd = withSublogger (LoggerName "withdraw") $ do
    incWithDrawn (wd ^. wAmount)
    logInfo ((wd ^. to show . packed) <> " withdrawn")
    return WithDrawlResult

deposit :: (MonadFaucet c m) => DepositRequest -> m DepositResult
deposit dr = withSublogger (LoggerName "deposit") $ do
    decrWithDrawn (dr ^. dAmount)
    logInfo ((dr ^. to show . packed) <> " deposited")
    return DepositResult

server :: ServerT API M
server = withdraw :<|> deposit

serverAPI :: Proxy API
serverAPI = Proxy
