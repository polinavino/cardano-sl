{ nixpkgs ? import <nixpkgs> {} }:
let
  inherit (nixpkgs) pkgs lib;
  haskellLib = pkgs.haskell.lib;

  include =  lib.flip lib.sources.sourceByRegex;
  exclude = regexes: src: lib.sources.cleanSourceWith {
    filter = (path: type:
      let relPath = lib.removePrefix (toString src + "/") (toString path);
      in !(lib.any (re: builtins.match re relPath != null) regexes));
    inherit src;
  };

  pkgsSuper = import ../. {};

  cardanoPkgs = (pkgsSuper.override {
    overrides = self: super: {
      cardano-sl-faucet = super.callPackage ./. {};
      # This is the long form way of doing what we're trying to get to
      # with mapAttrs below.
      cardano-sl-wallet =
        haskellLib.overrideSrc super.cardano-sl-wallet {
          src = exclude ["dist" "\.stack-work" "\.dir-locals.el"]
                        super.cardano-sl-wallet.src;
          };

    };
  });
  # ideally we want to be able to update all the packages in the set in one go.
  # unfortunately this isn't tying the recursive knot in some way
  #
  # drv = (lib.mapAttrs (name: drv: drv.overrideDerivation
  #         (o: { src = exclude ["dist" "\.stack-work" "\.dir-locals.el"] o.src;})) cardanoPkgs);
  drv = cardanoPkgs;
in
  if pkgs.lib.inNixShell
    then drv.cardano-sl-faucet.env
    # else drv
    # export some stuff for poking around in nix-repl
    else
      { inherit include exclude pkgsSuper;
        inherit (lib.sources) sourceByRegex cleanSourceWith;
        cardanoPkgs = drv;
      }
