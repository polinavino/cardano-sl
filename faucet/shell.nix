let
  localLib = import ../lib.nix;
in
{ system ? builtins.currentSystem
, config ? {}
, nixpkgs ? (import (localLib.fetchNixPkgs) { inherit system config; })
}:
let
  inherit (nixpkgs) pkgs lib;
  haskellLib = pkgs.haskell.lib;

  # include =  lib.flip lib.sources.sourceByRegex;
  # exclude = regexes: src: lib.sources.cleanSourceWith {
  #   filter = (path: type:
  #     let relPath = lib.removePrefix (toString src + "/") (toString path);
  #     in !(lib.any (re: builtins.match re relPath != null) regexes));
  #   inherit src;
  # };

  pkgsSuper = import ../. {};

  cardanoPkgs = (pkgsSuper.override {
    overrides = self: super: {
      cardano-sl-faucet = super.callPackage ./. {};
      # This is the long form way of doing what we're trying to get to
      # with mapAttrs below.
      # cardano-sl-wallet =
      #   haskellLib.overrideSrc super.cardano-sl-wallet {
      #     src = exclude ["dist" "\.stack-work" "\.dir-locals.el"]
      #                   super.cardano-sl-wallet.src;
      #     };

      mkDerivation = args: super.mkDerivation (args // lib.optionalAttrs (args ? src){
         src = let
            cleanSourceFilter = with pkgs.stdenv;
              name: type: let baseName = baseNameOf (toString name); in ! (
                # Filter out .git repo
                (type == "directory" && baseName == ".git") ||
                # Filter out editor backup / swap files.
                lib.hasSuffix "~" baseName ||
                builtins.match "^\\.sw[a-z]$" baseName != null ||
                builtins.match "^\\..*\\.sw[a-z]$" baseName != null ||
                # Filter out locally generated/downloaded things.
                baseName == "dist" ||
                # Filter out the files which I'm editing often.
                lib.hasSuffix ".nix" baseName ||
                # Filter out nix-build result symlinks
                (type == "symlink" && lib.hasPrefix "result" baseName)
              );
           in
             if (builtins.typeOf args.src) == "path"
               then builtins.filterSource cleanSourceFilter args.src
               else args.src or null;
        });
    };
  });
in
  if pkgs.lib.inNixShell
    then cardanoPkgs.cardano-sl-faucet.env
    else cardanoPkgs.cardano-sl-faucet
