with builtins;
with rec {
  pkgs    = import <nixpkgs> {};
  support = import ./. {};
  hs      = if getEnv "HASKELL_PACKAGES" == ""
               then support.haskellPackages
               else import (getEnv "HASKELL_PACKAGES");
  pkg     = getEnv "DIR";
  hsPkgs  = hs.override { overrides = support.hsOverride; };
};
hsPkgs.ghcWithPackages (h: [
  h.AstPlugin h.mlspec h.mlspec-helper h.QuickCheck h.quickspec
  (h.callPackage pkg {})
])
