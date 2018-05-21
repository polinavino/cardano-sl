module Test.Pos.Core.TxInWitnessGT where
import           Universum as U

import           Cardano.Crypto.Wallet (XSignature, xsignature)
import           Codec.CBOR.Read (deserialiseFromBytes)
import           Pos.Binary.Class
import           Pos.Binary.Core()
import           Pos.Core.Common (Address (..), Script (..) , IsBootstrapEraAddr (..), Coin (..)
                                 , makePubKeyAddress)
import           Pos.Core.Txp (TxInWitness (..), Tx (..), TxIn (..), TxOut (..))
import           Pos.Crypto.Configuration
import           Pos.Crypto.Hashing (unsafeHash)
import           Pos.Crypto.Signing  (RedeemPublicKey (..), PublicKey (..), RedeemSignature (..)
                                     , redeemPkBuild, Signature (..), parseFullPublicKey, deterministicKeyGen
                                     , SecretKey (..))
import           Pos.Data.Attributes (mkAttributes)
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
--TODO: add fst not null to the third condition, you can remove then remove the first.
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

{-
need to import Pos.Core.Txp for all the relevant types

forAll :: (Monad m, Show a, HasCallStack) => Gen a -> PropertyT m a
Generates a random input for the test by running the provided generator.


data TxInWitness
    = PkWitness { twKey :: !PublicKey
                , twSig :: !TxSig }
    | ScriptWitness { twValidator :: !Script
                    , twRedeemer  :: !Script }
    | RedeemWitness { twRedeemKey :: !RedeemPublicKey
                    , twRedeemSig :: !(RedeemSignature TxSigData) }
    | UnknownWitnessType !Word8 !ByteString
    deriving (Eq, Show, Generic, Typeable)

PkWitness <$> arbitrary <*> genSignature pm arbitrary

-- | 'Signature' of addrId.
type TxSig = Signature TxSigData

data TxSigData = TxSigData
    { -- | Transaction that we're signing
      txSigTxHash      :: !(Hash Tx)
    }
    deriving (Eq, Show, Generic, Typeable
    )
data Tx = UnsafeTx
    { _txInputs     :: !(NonEmpty TxIn)  -- ^ Inputs of transaction.
    , _txOutputs    :: !(NonEmpty TxOut) -- ^ Outputs of transaction.
    , _txAttributes :: !TxAttributes     -- ^ Attributes of transaction
    } deriving (Eq, Ord, Generic, Show, Typeable)


module Pos.Arbitrary.Txp
^^ need that to build proper tx (build proper tx function)

signTx :: HasConfiguration => (SecretKey, TxId) -> TxSig
signTx (sk, thash) = sign protocolMagic SignTx sk txSigData
  where
    txSigData = TxSigData
        { txSigTxHash = thash
        }

type TxId = Hash Tx

type Hash = AbstractHash Blake2b_256 (from Pos.Crypto.Hashing)

in Pos.Crypto.Signing.Signing
sign
    :: (Bi a)
    => ProtocolMagic
    -> SignTag         -- ^ See docs for 'SignTag'
    -> SecretKey
    -> a
    -> Signature a
sign pm t k = coerce . signRaw pm (Just t) k . Bi.serialize'

Note:

signTx gives a TxSig which is = Signature TxSigData. Need to gen TxId = Hash Tx
--> need to gen (SecretKey, TxId)
--> TxId first -> use `hash` Tx --> need to build Tx


data TxIn
    = TxInUtxo
    { -- | Which transaction's output is used
      txInHash  :: !TxId
      -- | Index of the output in transaction's outputs
    , txInIndex :: !Word32
    }
    | TxInUnknown !Word8 !ByteString

data TxOut = TxOut
    { txOutAddress :: !Address
    , txOutValue   :: !Coin
    } deriving (Eq, Ord, Generic, Show, Typeable)
*******
Aside: You have to start with a coinbase tx, look at how bitcoin did it to get an idea, perhaps in the cardano repo there is
also a coinbase tx. This will generate the relevant hashes etc.
*******
----------------------------------------------------------------------

buildProperTx
    :: ( )
    => ProtocolMagic
    -> NonEmpty (Tx, SecretKey, SecretKey, Coin)
    -> (Coin -> Coin, Coin -> Coin)
    -> NonEmpty (Tx, TxIn, TxOutAux, TxInWitness)
buildProperTx pm inputList (inCoin, outCoin) =
    txList <&> \(tx, txIn, fromSk, txOutput) ->
        ( tx
        , txIn
        , TxOutAux txOutput
        , mkWitness fromSk
        )
  where
    fun (UnsafeTx txIn txOut _, fromSk, toSk, c) =
        let inC = inCoin c
            outC = outCoin c
            txToBeSpent =
                UnsafeTx
                    txIn
                    ((makeTxOutput fromSk inC) <| txOut)
                    (mkAttributes ())
        in ( txToBeSpent
           , TxInUtxo (hash txToBeSpent) 0
           , fromSk
           , makeTxOutput toSk outC )
    -- why is it called txList? I've no idea what's going on here (@neongreen)
    txList = fmap fun inputList
    newTx = UnsafeTx ins outs def
    newTxHash = hash newTx
    ins  = fmap (view _2) txList
    outs = fmap (view _4) txList
    mkWitness fromSk = PkWitness
        { twKey = toPublic fromSk
        , twSig = sign pm SignTx fromSk TxSigData {
                      txSigTxHash = newTxHash } }
    makeTxOutput s c =
        TxOut (makePubKeyAddress (IsBootstrapEraAddr True) $ toPublic s) c

What is happening:
*<&> is flip fmap
* This is an infix alias for cons.
  >>> a <| []
  [a]
*fromSk and toSk represent the payer and the payee respectively
* >>> view _2 (1,"hello") <-- Control.Lens.Getter
  "hello"
* TxOutAux appears to be a wrapper for TxOut

txList is built using `fun`
    `fun` I think unmasks the coins to get your `Word64` (I think both arguements are therefore `getCoin`) <---- txToBeSpent
    The input that will be spent is constructed (i.e you build the tx that references the output you own)
        makeTxOutput will create an address from the secretkey you provided (makePubKeyAddress), and then use toPublic to give a publickey address
        and use coin amount (c) unmasked from inC
        You add this to the existing outputs (if any) in that particular `Tx`
        mkAttributes () <-- I assume means no tx attributes
    `fun` results in (txToBeSpent(constructed above), the tx input (which you just created above), the secretKey that owns the tx input
                     , (an output constructed with toSk, this represents the payee (note inC & outC are necessarily the same), index = 0)
    newTx = UnsafeTx ins outs def <-- the new tx, ins and outs are made with lenses and are taken from the results of `fun`
    newTxHash = hash newTx <-- self explanatory
    mkWitness constructs the relevant `PkWitness`

WHERE ARE YOU? Figuring out the weird module conflict thing that says you are not importing the right Tx constructor.

-}

-- First you are adding a txoutput assigned to you. So the first input is a coinbase tx.

-- | The Tx hash in this case is just the hash of the address. Amount in the output set to 0 because it does
-- not matter for property testing at the moment.

buildTxInput :: NonEmpty (Tx, SecretKey, SecretKey, Coin)
buildTxInput = case U.nonEmpty [(coinbaseTx, fromSecretKey, toSecretKey, amtToSpend)] of
                   Just correct -> correct
                   Nothing -> error "buildTxInput list is empty"

amtToSpend :: Coin
amtToSpend = Coin 100

fromSecretKey :: SecretKey
fromSecretKey = snd $ deterministicKeyGen "fromfromfromfromfromfromfromfrom"

toSecretKey :: SecretKey
toSecretKey = snd $ deterministicKeyGen "totototototototototototototototo"

coinbaseTx :: Tx
coinbaseTx = UnsafeTx txin utxo (mkAttributes ())


utxo :: (NonEmpty TxOut)
utxo = case U.nonEmpty [(TxOut testPubKeyAddress (Coin 0))] of
                Just output -> output
                Nothing -> error "UTXO list is empty."

txin :: (NonEmpty TxIn)
txin = case U.nonEmpty [(TxInUtxo (unsafeHash testPubKeyAddress) 0)] of
                Just input -> input
                Nothing -> error "Input list is empty."

testPubKeyAddress :: Address
testPubKeyAddress = makePubKeyAddress (IsBootstrapEraAddr True) (fst $ deterministicKeyGen "10101010101010101010101010101010")

--initAddress :: Address
--initAddress = makePubKeyAddress (IsBootstrapEraAddr True)


{-

Types in buildProper

-- | Coin is the least possible unit of currency.
newtype Coin = Coin
    { getCoin :: Word64
    } deriving (Show, Ord, Eq, Generic, Hashable, Data, NFData)

what is fromSk and toSk? They are labels, maybe you need two secret keys to generate a legitamite tx without a coinbase tx?

-- | Create a public key from a secret key
toPublic :: SecretKey -> PublicKey


-}



pM :: ProtocolMagic
pM = ProtocolMagic {getProtocolMagic = -22673}




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
            Left err -> U.error ((ST.pack "Error parsing public key:") `ST.append` err)

pkWitness :: TxInWitness
pkWitness = PkWitness pubKey (Signature txSig)

sPkWit :: LB.ByteString
sPkWit = toLazyByteString $ encode pkWitness

dsPkWitness :: TxInWitness
dsPkWitness = case (deserialiseFromBytes (decode :: Decoder s TxInWitness) sPkWit) of
                  Right ds -> snd ds
                  Left dsf -> P.error $ "Deserialization of PkWitness has failed:" ++ P.show dsf

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

