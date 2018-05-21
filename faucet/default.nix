{ mkDerivation, aeson, base, base16-bytestring, bytestring
, cardano-sl-core, cardano-sl-crypto, cardano-sl-wallet
, cardano-sl-wallet-new, connection, cryptonite, data-default, ekg
, ekg-core, ekg-statsd, exceptions, http-client, http-client-tls
, lens, log-warper, memory, mmorph, mtl, optparse-applicative
, QuickCheck, serokell-util, servant, servant-client
, servant-client-core, servant-server, servant-swagger
, servant-swagger-ui, stdenv, swagger2, text, text-format, tls, wai
, wai-cors, wai-extra, warp
}:
mkDerivation {
  pname = "cardano-sl-faucet";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    aeson base base16-bytestring bytestring cardano-sl-core
    cardano-sl-crypto cardano-sl-wallet cardano-sl-wallet-new
    connection cryptonite data-default ekg-core ekg-statsd exceptions
    http-client http-client-tls lens log-warper memory mmorph mtl
    QuickCheck serokell-util servant servant-client servant-client-core
    servant-server servant-swagger servant-swagger-ui swagger2 text
    text-format tls
  ];
  executableHaskellDepends = [
    base cardano-sl-core cardano-sl-wallet cardano-sl-wallet-new ekg
    ekg-core ekg-statsd exceptions lens log-warper mmorph mtl
    optparse-applicative servant servant-client servant-server text wai
    wai-cors wai-extra warp
  ];
  testHaskellDepends = [ base cardano-sl-wallet QuickCheck ];
  license = stdenv.lib.licenses.mit;
}
