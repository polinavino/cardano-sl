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

import           Pos.Core (Address (..))
import           Cardano.Wallet.API.V1.Types (V1(..), unV1)
import           Cardano.Wallet.API.Response (WalletResponse(..))
import           Cardano.Faucet.Types
import qualified Cardano.WalletClient as Client
-- import           Client.Cardano.Wallet.Web.Run     (runEndpointClient)

type API = "withdraw" :> ReqBody '[JSON] WithDrawlRequest :> Post '[JSON] WithDrawlResult
      :<|> "deposit" :> ReqBody '[JSON] DepositRequest :> Post '[JSON] DepositResult

withdraw :: (MonadFaucet c m) => WithDrawlRequest -> m WithDrawlResult
withdraw wd = withSublogger (LoggerName "withdraw") $ do
    resp <- Client.withdraw (wd ^. wAddress) (wd ^. wAmount)
    case resp of
        Left err -> do
            logError ("Error withdrawing " <> (wd ^. to show . packed)
                                           <> " error: "
                                           <> (err ^. to show . packed))
            return $ WithdrawlError err
        Right wr -> do
            let txn = wrData wr
            logInfo ((wd ^. to show . packed) <> " withdrawn. txn: "
                                              <> (txn ^. to show . packed))
            incWithDrawn (wd ^. wAmount . to unV1)
            return $ WithdrawlSuccess txn

deposit :: (MonadFaucet c m) => DepositRequest -> m DepositResult
deposit dr = withSublogger (LoggerName "deposit") $ do
    decrWithDrawn (dr ^. dAmount)
    logInfo ((dr ^. to show . packed) <> " deposited")
    return DepositResult

server :: ServerT API M
server = withdraw :<|> deposit

serverAPI :: Proxy API
serverAPI = Proxy
