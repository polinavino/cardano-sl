{ nixpkgs ? import <nixpkgs> {} }:
let
  inherit (nixpkgs) pkgs;
  cardanoPkgs = ((import ../default.nix {}).override {
    overrides = self: super: {
      cardano-sl-faucet = self.callPackage ./. {};

    };
  });
  drv = cardanoPkgs.cardano-sl-faucet;
in
  if pkgs.lib.inNixShell then drv.env else drv
