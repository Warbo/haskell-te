# Make sure you use 'NIX_PATH="$(./nix-support/nixPath.sh)" or equivalent!
with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "haskell-te";
  buildInputs = [ cabal2nix cabal2db explore-theories mlspec-bench ];
}
