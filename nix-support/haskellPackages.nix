{ hsOverride, nixpkgs }:

with builtins // {
  ghcVersion = nixpkgs.haskellPackages.ghc.version;
  reqVersion = "7.10.3";
};

assert ghcVersion == reqVersion ||
       abort "We require GHC ${reqVersion}, using GHC ${ghcVersion}";

{
  value = nixpkgs.haskellPackages.override {
            overrides = hsOverride (_: _: {});
          };
  removeOverrides = true;  # Otherwise they'd mess up the Haskell overrides
}
