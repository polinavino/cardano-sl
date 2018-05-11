{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module Main where

import Control.Lens
import           Network.Wai.Handler.Warp (run)
import           Servant

import           Pos.Wallet.Web.ClientTypes.Types (CAccountId (..))
import           Cardano.Faucet
import System.Remote.Monitoring (forkServer, serverMetricStore)
import           System.Remote.Monitoring.Statsd (defaultStatsdOptions, forkStatsd)

main :: IO ()
main = do
  ekg <- forkServer "localhost" 8001
  let c = mkFaucetConfig "wallet-url" (CAccountId "wallet-id") defaultStatsdOptions
  fEnv <- initEnv c (serverMetricStore ekg)
  _statsd <- forkStatsd (c ^. fcStatsdOpts) (fEnv ^. feStore)
  run 8081 (serve serverAPI $ s fEnv)
  where
      s env = hoistServer serverAPI (runM env) server
