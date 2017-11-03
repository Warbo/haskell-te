# Looks up info from the environment, returns a Haskell package set for nix-eval
# to use during exploration
with builtins;
with rec {
  support = import ./. {};
  hs      = if getEnv "HASKELL_PACKAGES" == ""
               then support.haskellPackages
               else import (getEnv "HASKELL_PACKAGES");
  hsDirs  = fromJSON (getEnv "OUT_DIRS");
  hsPkgs  = hs.override {
    overrides = support.hsOverride (self: super: listToAttrs (map
      (d: {
        value = self.callPackage d {};
        name  = support.pkgName (support.haskellPackages.callPackage d {}).name;
      })
      hsDirs));
  };
};

assert all (d: typeOf d == "path" || (isString d && substring 0 1 d == "/"))
           hsDirs || abort "Value of 'OUT_DIRS' is '${toJSON hsDirs}'";
hsPkgs
