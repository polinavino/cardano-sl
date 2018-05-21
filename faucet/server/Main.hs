{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module Main where

import Control.Lens
import           Network.Wai.Handler.Warp (run)
import           Servant

import Control.Monad.Except
-- import           Cardano.Wallet.API.V1.Types (PaymentSource (..), WalletId(..), AccountIndex)
import           Cardano.Faucet
import System.Remote.Monitoring (forkServer, serverMetricStore)
import           System.Remote.Monitoring.Statsd (forkStatsd)

main :: IO ()
main = do
  ekg <- forkServer "localhost" 8001
  let c = testFC -- mkFaucetConfig "wallet-url" 8000 (PaymentSource w idx) defaultStatsdOptions "./logging.cfg"
  fEnv <- initEnv c (serverMetricStore ekg)
  _statsd <- forkStatsd (c ^. fcStatsdOpts) (fEnv ^. feStore)
  run 8081 (serve serverAPI $ s fEnv)
  where
      nat :: FaucetEnv -> M a -> Handler a
      nat e = Handler . ExceptT . runM e
      s env = hoistServer serverAPI (nat env) server
