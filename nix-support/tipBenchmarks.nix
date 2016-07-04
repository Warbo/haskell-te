{ callPackage, defaultClusters, haskellPackages, nixFromCabal, processPackage,
  runScript, storeResult, writeScript }:

rec {
  te-benchmark = callPackage ../packages/te-benchmark {};

  path  = ../packages/te-benchmark;

  module = runScript { buildInputs = [ te-benchmark ]; } ''
    set -e

    OUT_DIR="$PWD/tip-benchmark-sig"
    export OUT_DIR

    mkdir -p "$OUT_DIR"

    cp -ra "${path}" ./te-benchmark
    chmod +w te-benchmark -R
    patchShebangs te-benchmark

    cd te-benchmark
    ./full_haskell_package.sh

    "${storeResult}" "$OUT_DIR"
  '';

  pkgDef = nixFromCabal (toString module) null;

  pkg = haskellPackages.callPackage pkgDef {};

  process = { clusters ? defaultClusters, quick ? true, sampleSize ? null }:
              processPackage { inherit clusters quick sampleSize; }
                             pkg.name pkg;
}
