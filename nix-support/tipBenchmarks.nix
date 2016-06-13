{ runScript, storeResult }:

rec {
  path  = ../packages/te-benchmark;

  rawHaskell = runScript {} ''
    DIR="$PWD"

    cd "${path}"
    ./mk_all_defs.sh > "$DIR/A.hs"

    "${storeResult}" "$DIR/A.hs"
  '';
}
