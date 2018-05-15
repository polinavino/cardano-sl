let
  localLib = import ../lib.nix;
in
{ system ? builtins.currentSystem
, config ? {}
, nixpkgs ? (import (localLib.fetchNixPkgs) { inherit system config; })
}:
let
  inherit (nixpkgs) pkgs lib;
  cardanoPkgs = import ../. {};
in
  if pkgs.lib.inNixShell
    then cardanoPkgs.cardano-sl-faucet.env
    else cardanoPkgs.cardano-sl-faucet
