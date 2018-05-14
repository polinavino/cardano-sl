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
import           Client.Cardano.Wallet.Web.Api     (newPayment)
import           Client.Cardano.Wallet.Web.Run     (runEndpointClient)

type API = "withdraw" :> ReqBody '[JSON] WithDrawlRequest :> Post '[JSON] WithDrawlResult
      :<|> "deposit" :> ReqBody '[JSON] DepositRequest :> Post '[JSON] DepositResult

withdraw :: (MonadIO m, MonadReader c m, HasFaucetEnv c) => WithDrawlRequest -> m WithDrawlResult
withdraw wd = do
    incWithDrawn (wd ^. wAmount)
    liftIO $ print $ wd
    return WithDrawlResult

deposit :: (MonadIO m, MonadReader c m, HasFaucetEnv c) => DepositRequest -> m DepositResult
deposit dr = do
    decrWithDrawn (dr ^. dAmount)
    liftIO $ print dr
    return DepositResult

server :: ServerT API M
server = withdraw :<|> deposit

serverAPI :: Proxy API
serverAPI = Proxy
