{ hsOverride, nixpkgs }:

with builtins // {
  ghcVersion = nixpkgs.haskellPackages.ghc.version;
  reqVersion = "7.10.3";
};

assert ghcVersion == reqVersion ||
       abort "Using GHC ${ghcVersion} (should be ${reqVersion})";

# We return a list to prevent 'makeOverridable' breaking our overrides
[ (nixpkgs.haskellPackages.override { overrides = hsOverride; }) ]
