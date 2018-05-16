module Cardano.WalletClient where
    -- ( export
    -- , export
    -- ) where

import           Control.Lens
import           Control.Monad.Reader
import Data.List.NonEmpty (NonEmpty(..))
import           Cardano.Faucet.Types
import           Cardano.Wallet.API.V1.Types (Payment (..), PaymentDistribution (..),
                                              PaymentSource (..), V1(..))
-- import           Cardano.Wallet.API.V1.Types.V1 (Coin (..), Address(..))
import           Cardano.Wallet.Client (Resp, Transaction, WalletClient (..), WalletResponse (..),
                                        liftClient)
import           Pos.Wallet.Web.Methods.Payment (newPayment)
import           Pos.Core (Coin (..), Address(..))
import           Pos.Wallet.Web.ClientTypes.Types (Addr (..), CId (..))


withdraw :: (HasFaucetEnv e, MonadReader e m, MonadIO m) => V1 Address -> V1 Coin -> Resp m Transaction
withdraw addr coin = do
    paymentSource <- view (feFaucetConfig . fcFaucetPaymentSource)
    client <- liftClient <$> view feWalletClient
    let paymentDist = (PaymentDistribution addr coin :| [])
        payment = Payment paymentSource paymentDist Nothing Nothing
    postTransaction client payment
