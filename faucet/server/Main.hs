module Main where

import Servant
import Servant.Server
import Network.Wai.Handler.Warp (run)

import Cardano.Faucet

main = run 8081 (serve serverAPI server)
