{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Cardano.WalletClient where
    -- ( export
    -- , export
    -- ) where

import Crypto.Hash (Blake2b, Blake2b_224, Blake2b_256, Digest)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Base16 as Base16
import qualified Data.ByteArray as BA
-- import qualified Serokell.Util.Base16 as Base16
import qualified Crypto.Hash as CryptoHash
import           Control.Lens
import           Control.Monad.Reader
import Data.Text (Text)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Text.Buildable (build)
import           Cardano.Faucet.Types
import           Cardano.Wallet.API.V1.Types (Payment (..), PaymentDistribution (..),
                                              PaymentSource (..), V1(..), mkPassPhrase)
-- import           Cardano.Wallet.API.V1.Types.V1 (Coin (..), Address(..))
import           Cardano.Wallet.Client (Resp, Transaction, WalletClient (..), WalletResponse (..),
                                        liftClient)
import           Pos.Wallet.Web.Methods.Payment (newPayment)
import           Pos.Core (Coin (..), Address(..))
import Pos.Crypto.Signing (PassPhrase(..))
import           Pos.Wallet.Web.ClientTypes.Types (Addr (..), CId (..))


withdraw :: (MonadFaucet c m) => V1 Address -> V1 Coin -> Resp m Transaction
withdraw addr coin = do
    paymentSource <- view (feFaucetConfig . fcFaucetPaymentSource)
    client <- liftClient <$> view feWalletClient
    let paymentDist = (PaymentDistribution addr coin :| [])
        payment = Payment paymentSource paymentDist Nothing sp
    postTransaction client payment
  where
    sp :: Maybe (V1 PassPhrase)
    sp = Just $ V1 $ hashPwd "XXX" -- TODO: get from config

hashPwd :: ByteString -> PassPhrase
hashPwd  bs =
    let blake = CryptoHash.hash bs :: Digest (Blake2b_256)
    in BA.convert blake
