{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wall #-}
module Cardano.Faucet (
    server
  , serverAPI
  , module Cardano.Faucet.Types
  ) where

import Control.Lens
import           Control.Monad.IO.Class
import           Control.Monad.Reader
import           Servant

import           Cardano.Faucet.Types

type API = "withdraw" :> ReqBody '[JSON] WithDrawlRequest :> Post '[JSON] WithDrawlResult
      :<|> "deposit" :> ReqBody '[JSON] DepositRequest :> Post '[JSON] DepositResult

withdraw :: (MonadIO m, MonadReader c m, HasConfig c) => WithDrawlRequest -> m WithDrawlResult
withdraw wd = do
    url <- view walletApiURL
    liftIO $ putStrLn $ (show wd) ++ " -- " ++ url
    return WithDrawlResult

deposit :: (MonadIO m, MonadReader c m, HasConfig c) => DepositRequest -> m DepositResult
deposit dr = do
    liftIO $ print dr
    return DepositResult

server :: ServerT API M
server = withdraw :<|> deposit

serverAPI :: Proxy API
serverAPI = Proxy
