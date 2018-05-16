module Test.Pos.Core.TxInWitnessGT
       ( goldenTestSuite
       ) where

import           Universum as U

import           Cardano.Crypto.Wallet (XSignature, xsignature)
import           Codec.CBOR.Read (deserialiseFromBytes)
import           Pos.Binary.Class
import           Pos.Binary.Core()
import           Pos.Core.Common
import           Pos.Core.Txp (TxInWitness (..))
import           Pos.Crypto.Signing  (RedeemPublicKey (..), PublicKey (..), RedeemSignature (..)
                                     , redeemPkBuild, Signature (..), parseFullPublicKey)
import           System.FilePath ((</>))
import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.Golden (goldenVsFile)

import qualified Crypto.Sign.Ed25519 as Ed25519
import qualified Data.ByteString.Lazy as LB
import qualified Data.ByteString.Base16 as SHD
import qualified Data.ByteString.Base16.Lazy as LHD
import qualified Data.Text as ST
import qualified Prelude as P (writeFile, show, error)



goldenTestSuite :: TestTree
goldenTestSuite =
    testGroup "Serialization & Deserialization of TxInWitness"
        [ goldenVsFile "Serialization of PkWitness"
            (goldenPath ++ "sPkWitness.golden") (goldenPath ++ "sPkWitness.test")
            sPkWitTestOutput
        , goldenVsFile "Deserialization of PkWitness"
             (goldenPath ++ "dsPkWitness.golden") (goldenPath ++ "dsPkWitness.test")
             dsPkWitTestOutput
        , goldenVsFile "Serialization of ScriptWitness"
             (goldenPath ++ "sSriptWit.golden") (goldenPath ++ "sSriptWit.test")
             sSWitTestOutput
        , goldenVsFile "Deserialization of ScriptWitness"
            (goldenPath ++ "dsScriptWit.golden") (goldenPath ++ "dsScriptWit.test")
            dsSWitTestOutput
        , goldenVsFile "Serialization of RedeemWitness"
            (goldenPath ++ "sRedeemWit.golden") (goldenPath ++ "sRedeemWit.test")
            sRedeemWitTestOutput
        , goldenVsFile "Deserialization of RedeemWitness"
            (goldenPath ++ "dsRedeemWit.golden") (goldenPath ++ "dsRedeemWit.test")
            dsRedeemWitTestOutput
        , goldenVsFile "Serialization of UnknownWitnessType"
            (goldenPath ++ "sUnWitType.golden") (goldenPath ++ "sUnWitType.test")
            sUnWitTypeTestOutput
        , goldenVsFile "Deserialization of UnknownWitnessType"
            (goldenPath ++ "dsUnWitType.golden") (goldenPath ++ "dsUnWitType.test")
            dsUnWitTypeTestOutput
        ]

--------------- Misc ---------------

hexFormatFunc :: LB.ByteString -> LB.ByteString
hexFormatFunc bs
    | LB.length bs <= 32 = bs
    | lengthOfRem >= 32 = (fst splitTupleBS `LB.append` "\n") `LB.append` (hexFormatFunc $ snd splitTupleBS)
    | lengthOfRem < 32  = snd splitTupleBS
    | otherwise = bs
  where
    splitTupleBS = LB.splitAt 32 bs
    lengthOfRem = (LB.length $ snd splitTupleBS)


goldenPath :: String
goldenPath = "test/Test/Pos/Core/CoreGoldenFiles/"

-- | In the functions and values below, s prefix = serialized, ds prefix = deserialized.

--------------- PK WITNESS ---------------

sig :: ByteString
sig =  fst $ SHD.decode "6b327b445ae7063bfd8769132ef21862\
                       \edad13ac2a77a1ce3c6d589c7ea67c95\
                       \3c4e65ebc948a44b8c639b815aab2733\
                       \70edfb32b0e38bd70408764d2ac65d07"

txSig :: XSignature
txSig = case xsignature sig of
            Right xsig -> xsig
            Left err -> P.error $ "txSig error:" ++ err

testPubKey :: Text
testPubKey = "s6xMQZD0xKcBuOw2+OyMUporuSLMLi99mU3A6/9cRBrO/ekTq8oBbS7yf5OgbYg58HzO8ASRpzuaca8hED08VQ=="

-- | `pkWitness` was generated with arbitrary instances therefore the public key
-- does not correspond to the signature.

pubKey :: PublicKey
pubKey = case (parseFullPublicKey testPubKey) of
            Right pk -> pk
            Left err -> U.error ((ST.pack "Lulz") `ST.append` err)

pkWitness :: TxInWitness
pkWitness = PkWitness pubKey (Signature txSig)

sPkWit :: LB.ByteString
sPkWit = toLazyByteString $ encode pkWitness

dsPkWitness :: TxInWitness
dsPkWitness = case (deserialiseFromBytes (decode :: Decoder s TxInWitness) sPkWit) of
                  Right ds -> snd ds
                  Left dsf -> P.error $ "Deserialization of PkWitness has failed:" ++ P.show dsF

sPkWitTestOutput :: IO ()
sPkWitTestOutput = LB.writeFile (goldenPath </> "sPkWitness.test")  (hexFormatFunc $ LHD.encode sPkWit)

dsPkWitTestOutput :: IO ()
dsPkWitTestOutput = P.writeFile (goldenPath ++ "dsPkWitness.test")  (P.show dsPkWitness)

--------------- SCRIPT WITNESS ---------------

sWit :: TxInWitness
sWit = ScriptWitness validator redeemer

validator :: Script
validator = Script { scrVersion = 27565
                   , scrScript = "\NAK\231]\167]\178@{\155\178\&8\128\216\160#\216\129|\208\183yx\132\193EC"}

redeemer :: Script
redeemer = Script {scrVersion = 13334, scrScript = "\176\170I/\243_\147\202\DC3\237"}

sSWit :: LB.ByteString
sSWit = toLazyByteString $ encode sWit

dsSWit :: TxInWitness
dsSWit =
    case (deserialiseFromBytes (decode :: Decoder s TxInWitness) sSWit) of
        Right scriptWit -> snd scriptWit
        Left dsF        -> P.error $ "Deserialization of ScriptWitness has failed:" ++ P.show dsF

sSWitTestOutput :: IO ()
sSWitTestOutput = LB.writeFile (goldenPath </> "sSriptWit.test") (hexFormatFunc $ LHD.encode sSWit)

dsSWitTestOutput :: IO ()
dsSWitTestOutput = P.writeFile (goldenPath </> "dsScriptWit.test")  (P.show dsSWit)


--------------- RedeemWitness --------------


redeemPublicKey :: RedeemPublicKey
redeemPublicKey = redeemPkBuild "-\254\EMG-\170C\DC2\166*\183jT?\215\196/ID\SUB\133\230\CAN\197x\243\
                                 \\\(>\ESC\224\t"

redeemSig :: RedeemSignature a
redeemSig = RedeemSignature $ Ed25519.Signature "\249#A(\202\183\245\ESC\174\ETB\187\225\181\244\196\
                                                 \/194]\SI\201\196]\DLE\209\SOR>\242\206\166\179\222\
                                                 \206\212\159\STX\DC1P\208\&4\174X\193\184[#\220\DC2\
                                                 \184\&5\143\187w\252\157\213\189\198\133\SUB\229!\23\
                                                 \1\158\a"

redeemWit :: TxInWitness
redeemWit = RedeemWitness redeemPublicKey redeemSig

sRedeemWit :: LB.ByteString
sRedeemWit = toLazyByteString $ encode redeemWit

dsRedeemWit :: TxInWitness
dsRedeemWit =
    case (deserialiseFromBytes (decode :: Decoder s TxInWitness) sRedeemWit) of
        Right redWit -> snd redWit
        Left dsF     -> P.error $ "Deserialization of RedeemWitness has failed:" ++ P.show dsF

sRedeemWitTestOutput :: IO ()
sRedeemWitTestOutput = LB.writeFile (goldenPath </> "sRedeemWit.test")  (hexFormatFunc $ LHD.encode sRedeemWit)

dsRedeemWitTestOutput :: IO ()
dsRedeemWitTestOutput = P.writeFile (goldenPath </> "dsRedeemWit.test")  (P.show dsRedeemWit)


--------------- UnknownWitnessType ---------------


unWitType :: TxInWitness
unWitType = UnknownWitnessType 100 "test"

sUnWitType :: LB.ByteString
sUnWitType = toLazyByteString $ encode unWitType


dSunWitType :: TxInWitness
dSunWitType =
    case (deserialiseFromBytes (decode :: Decoder s TxInWitness) sUnWitType) of
        Right sUnWit -> snd sUnWit
        Left dsf     -> P.error $ "Deserialization of UnknownWitnessType has failed" ++ P.show dsf

sUnWitTypeTestOutput :: IO ()
sUnWitTypeTestOutput = LB.writeFile (goldenPath </> "sUnWitType.test") (hexFormatFunc $ LHD.encode sUnWitType)

dsUnWitTypeTestOutput :: IO ()
dsUnWitTypeTestOutput = P.writeFile (goldenPath </> "dsUnWitType.test") (P.show dSunWitType)

