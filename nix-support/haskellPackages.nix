# Note that 'callPackage' will pollute the result, so use 'import'.
{ hsOverride, nixpkgs }:

with builtins // {
  ghcVersion = nixpkgs.haskellPackages.ghc.version;
  reqVersion = "7.10.3";
};

assert ghcVersion == reqVersion ||
       abort "We require GHC ${reqVersion}, using GHC ${ghcVersion}";

nixpkgs.haskellPackages.override { overrides = hsOverride (_: _: {}); }
