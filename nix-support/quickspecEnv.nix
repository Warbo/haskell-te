# Looks up info from the environment, returns a Haskell package set for nix-eval
# to use during exploration
with builtins;
with rec {
  support = import ./. {};
  hs      = if getEnv "HASKELL_PACKAGES" == ""
               then support.haskellPackages
               else import (getEnv "HASKELL_PACKAGES");
  pkg     = getEnv "OUT_DIR";
  pkgName = getEnv "PKG_NAME";
  hsPkgs  = hs.override {
    overrides = support.hsOverride (self: super: {
      "${pkgName}" = self.callPackage pkg {};
    });
  };
};

assert typeOf pkg == "path" || (isString pkg && substring 0 1 pkg == "/") ||
       abort "Value of 'OUT_DIR' is '${toJSON pkg}'";
hsPkgs
