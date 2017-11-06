{ hsOverride, nixpkgs, stable }:

with builtins // {
  ghcVersion = nixpkgs.haskellPackages.ghc.version;
  reqVersion = "7.10.3";
};

assert stable -> ghcVersion == reqVersion ||
       abort "Stable build requires GHC ${reqVersion}, using GHC";

{
  value = nixpkgs.haskellPackages.override {
            overrides = hsOverride (_: _: {});
          };
  removeOverrides = true;  # Otherwise they'd mess up the Haskell overrides
}
