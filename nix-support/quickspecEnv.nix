# Looks up info from the environment, returns a Haskell package set for nix-eval
# to use during exploration
with builtins;
with rec {
  pkgs    = import <nixpkgs> {};
  support = import ./. {};
  hs      = if getEnv "HASKELL_PACKAGES" == ""
               then support.haskellPackages
               else import (getEnv "HASKELL_PACKAGES");
  pkg     = getEnv "OUT_DIR";
  pkgName = getEnv "PKG_NAME";
  hsPkgs  = hs.override {
    overrides = self: super: (support.hsOverride self super) // {
      "${pkgName}" = self.callPackage pkg {};
    };
  };
};
hsPkgs
