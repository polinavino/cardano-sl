{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
module Cardano.Faucet where

import Servant
import Control.Monad.IO.Class

import Cardano.Faucet.Types

type API = "withdraw" :> ReqBody '[JSON] WithDrawlRequest :> Post '[JSON] WithDrawlResult
      :<|> "deposit" :> ReqBody '[JSON] DepositRequest :> Post '[JSON] DepositResult

withdraw :: MonadIO m => WithDrawlRequest -> m WithDrawlResult
withdraw wd = do
    liftIO $ print wd
    return WithDrawlResult

deposit :: (MonadIO m) => DepositRequest -> m DepositResult
deposit dr = do
    liftIO $ print dr
    return DepositResult

server :: (MonadIO m) => ServerT API m
server = withdraw :<|> deposit

serverAPI :: Proxy API
serverAPI = Proxy
