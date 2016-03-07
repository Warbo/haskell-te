# Make sure you use 'NIX_PATH="$(./nix-support/nixPath.sh)" or equivalent!
with import <nixpkgs> {};

stdenv.mkDerivation {
  name = "haskell-te";
  buildInputs = [
    annotatedb
    cabal2nix
    cabal2db
    explore-theories
    getDeps
    jq
    ML4HSFE
    mlspec-bench
    order-deps
    recurrent-clustering
  ];
}
