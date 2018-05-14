{ mkDerivation, aeson, base, cardano-sl-core, cardano-sl-wallet
, cardano-sl-wallet-new, ekg, ekg-core, ekg-statsd, lens, mtl
, optparse-applicative, servant, servant-client
, servant-client-core, servant-server, servant-swagger
, servant-swagger-ui, stdenv, swagger2, wai, wai-cors, wai-extra
, warp
}:
mkDerivation {
  pname = "cardano-sl-faucet";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    aeson base cardano-sl-core cardano-sl-wallet cardano-sl-wallet-new
    ekg-core ekg-statsd lens mtl servant servant-client
    servant-client-core servant-server servant-swagger
    servant-swagger-ui swagger2
  ];
  executableHaskellDepends = [
    base cardano-sl-wallet cardano-sl-wallet-new ekg ekg-core
    ekg-statsd lens mtl optparse-applicative servant servant-client
    servant-server wai wai-cors wai-extra warp
  ];
  testHaskellDepends = [ base cardano-sl-wallet ];
  license = stdenv.lib.licenses.mit;
}
