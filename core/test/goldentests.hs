import           Universum

import           Test.Pos.Core.TxInWitnessGT (goldenTestSuite)

import           Test.Tasty

main :: IO ()
main = defaultMain goldenTestSuite


