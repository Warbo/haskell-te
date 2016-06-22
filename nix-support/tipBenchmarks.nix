{ defaultClusters, haskellPackages, nixFromCabal, processPackage, runScript,
  storeResult, writeScript }:

rec {
  path  = ../packages/te-benchmark;

  module = runScript {} ''
    set -e

    OUT_DIR="$PWD/tip-benchmark-sig"
    export OUT_DIR

    mkdir -p "$OUT_DIR"

    cd "${path}"
    ./full_haskell_package.sh

    "${storeResult}" "$OUT_DIR"
  '';

  pkgDef = nixFromCabal (toString module) null;

  pkg = haskellPackages.callPackage pkgDef {};

  process = { clusters ? defaultClusters, quick ? true, sampleSize ? null }:
              processPackage { inherit clusters quick sampleSize; }
                             pkg.name pkg;
}
