{ runScript, storeResult, writeScript }:

rec {
  path  = ../packages/te-benchmark;

  module = runScript {} ''
    set -e

    OUT_DIR="tip-benchmark-sig"
    export OUT_DIR

    mkdir -p "$OUT_DIR"

    cd "${path}"
    ./full_haskell_package.sh

    "${storeResult}" "$OUT_DIR"
  '';
}
