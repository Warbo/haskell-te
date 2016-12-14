defs: with defs; with lib; with builtins;

with {
  cmd = "${package}/bin/mlspecBench";
};

mapAttrs (name: testRun name null { buildInputs = [ package ]; }) {
  canRun = ''
    "${cmd}" < ${./example.smt2} || exit 1
  '';

  outputIsJson = ''
    OUTPUT=$("${cmd}" < ${./example.smt2}) || exit 1
    TYPE=$(echo "$OUTPUT" | jq -r 'type') || {
      echo -e "START OUTPUT\n$OUTPUT\nEND OUTPUT" 1>&2
      exit 1
    }
    [[ "x$TYPE" = "xobject" ]] || {
      echo -e "START OUTPUT\n$OUTPUT\nEND OUTPUT" 1>&2
      echo "Type is '$TYPE' instead of object" 1>&2
      exit 1
    }
  '';

  haveEquations = ''
    OUTPUT=$("${cmd}" < ${./example.smt2})   || exit 1
     CHECK=$(echo "$OUTPUT" | jq 'has("result")') || exit 1
    [[ "x$CHECK" = "xtrue" ]] || {
      echo -e "Didn't find 'result' in\n$OUTPUT" 1>&2
      exit 1
    }
  '';

  filterSamples = let keepers = [
    { name = "append";          module = "A"; package = "tip-benchmark-sig"; }
    { name = "constructorNil";  module = "A"; package = "tip-benchmark-sig"; }
    { name = "constructorCons"; module = "A"; package = "tip-benchmark-sig"; }
  ];
  in ''
    set -e
    export BENCH_FILTER_KEEPERS='${toJSON keepers}'
    BENCH_OUT=$(CLUSTERS=1 "${cmd}" < ${../benchmarks/list-full.smt2})
    for S in append constructorNil constructorCons
    do
      echo "$BENCH_OUT" | jq '.result' | grep "$S" > /dev/null || {
        echo "No equations for '$S'" 1>&2
        exit 1
      }
    done
    for S in map foldl foldr length reverse
    do
      if echo "$BENCH_OUT" | jq '.result' | grep "$S" > /dev/null
      then
        echo "Found equation with forbidden symbol '$S'" 1>&2
        exit 1
      fi
    done
  '';
}
