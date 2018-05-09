{ mkDerivation, aeson, base, cardano-sl-wallet, lens, mtl, servant
, servant-client, servant-client-core, servant-server
, servant-swagger, servant-swagger-ui, stdenv, swagger2, wai
, wai-cors, wai-extra, warp
}:
mkDerivation {
  pname = "cardano-sl-faucet";
  version = "0.1.0.0";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    aeson base cardano-sl-wallet lens mtl servant servant-client
    servant-client-core servant-server servant-swagger
    servant-swagger-ui swagger2
  ];
  executableHaskellDepends = [
    base mtl servant servant-server wai wai-cors wai-extra warp
  ];
  testHaskellDepends = [ base ];
  license = stdenv.lib.licenses.mit;
}
