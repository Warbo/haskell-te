# Looks up info from the environment, returns a package with everything
# necessary to generate a QuickSpec 'runner'
with builtins;
with rec {
  pkgs    = import <nixpkgs> {};
  support = import ./. {};
  hs      = if getEnv "HASKELL_PACKAGES" == ""
               then support.haskellPackages
               else import (getEnv "HASKELL_PACKAGES");
  pkg     = getEnv "OUT_DIR";
  hsPkgs  = hs.override { overrides = support.hsOverride; };
};
hsPkgs.ghcWithPackages (h: [
  h.AstPlugin h.mlspec h.mlspec-helper h.nix-eval h.QuickCheck h.quickspec
  (h.callPackage pkg {})
])
