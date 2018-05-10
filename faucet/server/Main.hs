module Main where

import           Network.Wai.Handler.Warp (run)
import           Servant
import           Servant.Server

import           Cardano.Faucet
import           Cardano.Faucet.Types

main :: IO ()
main = do
  let c = mkConfig "test"
  run 8081 (serve serverAPI $ s c)
  where
      s c = hoistServer serverAPI (runM c) server
