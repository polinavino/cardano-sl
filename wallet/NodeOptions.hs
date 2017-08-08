{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE CPP           #-}
{-# LANGUAGE QuasiQuotes   #-}

-- | Command line options of wallet node.

module NodeOptions
       ( WalletNodeArgs (..)
       , WalletArgs (..)
       , getWalletNodeOptions
       ) where

import           Data.Version                 (showVersion)
import           Options.Applicative          (Parser, execParser, footerDoc,
                                               fullDesc, header, help, helper, info,
                                               infoOption, long, metavar,
                                               progDesc, strOption, switch,
                                               value)
import           Universum                    hiding (show)

import           Paths_cardano_sl             (version)
import qualified Pos.CLI                      as CLI
import           Pos.Client.CLI.NodeOptions   (SimpleNodeArgs (..), simpleNodeArgsParser, usageExample)

data WalletNodeArgs = WalletNodeArgs SimpleNodeArgs WalletArgs

data WalletArgs = WalletArgs
    { enableWeb                 :: !Bool
    , webPort                   :: !Word16
    , walletTLSCertPath         :: !FilePath
    , walletTLSKeyPath          :: !FilePath
    , walletTLSCAPath           :: !FilePath
    , enableWallet              :: !Bool
    , walletPort                :: !Word16
    , walletDbPath              :: !FilePath
    , walletRebuildDb           :: !Bool
    , walletDebug               :: !Bool
    } deriving Show

walletArgsParser :: Parser WalletNodeArgs
walletArgsParser = do
    simpleNodeArgs <- simpleNodeArgsParser
    enableWeb <- switch $
        long "web" <>
        help "Activate web API (it’s not linked with a wallet web API)."
    webPort <-
        CLI.webPortOption 8080 "Port for web API."
    walletTLSCertPath <- strOption $
        long    "tlscert" <>
        metavar "FILEPATH" <>
        value   "server.crt" <>
        help    "Path to file with TLS certificate"
    walletTLSKeyPath <- strOption $
        long    "tlskey" <>
        metavar "FILEPATH" <>
        value   "server.key" <>
        help    "Path to file with TLS key"
    walletTLSCAPath <- strOption $
        long    "tlsca" <>
        metavar "FILEPATH" <>
        value   "ca.crt" <>
        help    "Path to file with TLS certificate authority"
    enableWallet <- switch $
        long "wallet" <>
        help "Activate Wallet web API."
    walletPort <-
        CLI.walletPortOption 8090 "Port for Daedalus Wallet API."
    walletDbPath <- strOption $
        long  "wallet-db-path" <>
        help  "Path to the wallet's database." <>
        value "wallet-db"
    walletRebuildDb <- switch $
        long "wallet-rebuild-db" <>
        help "If wallet's database already exists, discard its contents \
             \and create a new one from scratch."
    walletDebug <- switch $
        long "wallet-debug" <>
        help "Run wallet with debug params (e.g. include \
             \all the genesis keys in the set of secret keys)."

    pure $ WalletNodeArgs simpleNodeArgs WalletArgs{..}

getWalletNodeOptions :: IO WalletNodeArgs
getWalletNodeOptions = execParser programInfo
  where
    programInfo = info (helper <*> versionOption <*> walletArgsParser) $
        fullDesc <> progDesc "Cardano SL main server node w/ wallet."
                 <> header "Cardano SL node."
                 <> footerDoc usageExample

    versionOption = infoOption
        ("cardano-node-" <> showVersion version)
        (long "version" <> help "Show version.")
