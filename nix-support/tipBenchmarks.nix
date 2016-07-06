{ bash, defaultClusters, haskellPackages, nixFromCabal,
  processPackage, racket, runScript, stdenv, storeResult, writeScript }:

rec {
  te-benchmark = import ../packages/te-benchmark {
                   inherit bash haskellPackages racket stdenv
                           writeScript;
                 };

  path  = ../packages/te-benchmark;

  module = runScript { buildInputs = [ te-benchmark ]; } ''
    set -e

    OUT_DIR="$PWD/tip-benchmark-sig"
    export OUT_DIR

    mkdir -p "$OUT_DIR"

    fullTePkg

    "${storeResult}" "$OUT_DIR"
  '';

  pkgDef = nixFromCabal (toString module) null;

  pkg = haskellPackages.callPackage pkgDef {};

  process = { clusters ? defaultClusters, quick ? true, sampleSize ? null }:
              processPackage { inherit clusters quick sampleSize; }
                             pkg.name pkg;
}
