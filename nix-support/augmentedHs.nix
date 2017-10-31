# Provides a set of Haskell packages for use by nix-eval.
{ hsDir }:

# We use "./.." so that all of our dependencies get included
with import ../nix-support {};
with builtins;
let hsName = "tip-benchmark-sig";  # The name used by full_haskell_package
    hsPkgs = haskellPackages.override {
      overrides = self: super:
        # Include existing overrides, along with our new one
        hsOverride self super // {
          "tip-benchmark-sig" = self.callPackage (toString (nixedHsPkg hsDir)) {};
        };
    };
    # Echo "true", with our Haskell package as a dependency
    check = stdenv.mkDerivation {
      name = "check-for-pkg";
      buildInputs  = [(hsPkgs.ghcWithPackages (h: [h."tip-benchmark-sig"]))];
      buildCommand = "source $stdenv/setup; echo true > $out";
    };
 in assert hsDir  != ""                 || abort "Got no OUT_DIR";
    assert hsPkgs ? "tip-benchmark-sig" || abort "hsPkgs doesn't have pkg";
    assert import check                 || abort "Couldn't build pkg";
    hsPkgs
