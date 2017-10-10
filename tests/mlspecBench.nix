defs: with defs; with lib; with builtins;

with rec {
  maxSecs  = "300";
  testFile = name: path: runCommand "mls-${name}"
    {
      buildInputs = [ fail jq package ];
      MAX_SECS    = maxSecs;
    }
    ''
      echo "Running ${name} through mlspecBench" 1>&2
      OUTPUT=$(mlspecBench < "${path}") ||
        fail "Couldn't explore ${name}"

      T=$(echo "$OUTPUT" |
          jq 'has("cmd") and has("info") and has("results")') ||
        fail "Couldn't parse output\nSTART\n$OUTPUT\nEND"

      [[ "x$T" = "xtrue" ]] ||
        fail "Required fields missing:\n$OUTPUT"
      mkdir "$out"
    '';
};

{
  list-full  = testFile "list-full"  ../benchmarks/list-full.smt2;
  nat-full   = testFile "nat-full"   ../benchmarks/nat-full.smt2;
  nat-simple = testFile "nat-simple" ../benchmarks/nat-simple.smt2;
} // mapAttrs (name: runCommand name {
                  buildInputs = [ fail jq package tipBenchmarks.tools ];
                  MAX_SECS    = maxSecs;
                }) {
  canRun = ''
    set -e
    mlspecBench < "${./example.smt2}"
    mkdir "$out"
  '';

  outputIsJson = ''
    set -e
    OUTPUT=$(mlspecBench < ${./example.smt2}) || exit 1
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
    set -e
    OUTPUT=$(mlspecBench < ${./example.smt2})   || exit 1
     CHECK=$(echo "$OUTPUT" | jq 'has("results")') || exit 1
    [[ "x$CHECK" = "xtrue" ]] || {
      echo -e "Didn't find 'results' in\n$OUTPUT" 1>&2
      exit 1
    }
  '';

  filterSamples =
    with {
      keepers = map (name: {
                      inherit name;
                      module  = "A";
                      package = "tip-benchmark-sig";
                    }) [ "append" "constructorNil" "constructorCons" ];
    };
    ''
      set -e

      BENCH_OUT=$(CLUSTERS=1 SAMPLE_SIZES="5" mlspecBench)

      # Get all the constant symbols in all equations
      STDOUTS=$(echo "$BENCH_OUT" | jq -r '.results | .[] | .stdout') ||
        fail "Couldn't get stdouts\n\n$BENCH_OUT"

      OUTPUTS=$(while read -r F
                do
                  cat "$F"
                done < <(echo "$STDOUTS")) ||
        fail "Couldn't concat stdouts\n\n$BENCH_OUT\n\n$STDOUTS"

      EQS=$(echo "$OUTPUTS" | grep -v '^Depth') ||
        fail "Couldn't get eqs\n\n$BENCH_OUT\n\n$OUTPUTS"

      NAMES=$(echo "$EQS" |
              jq -r 'getpath(paths(type == "object" and .role == "constant")) |
                     .symbol' |
              sort -u) || fail "Couldn't get names\n\n$BENCH_OUT\n\n$EQS"
      SAMPLE=$(choose_sample 5 1)

      # Remove any names which appear in the sample
      while read -r NAME
      do
        NAMES=$(echo "$NAMES" | grep -vFx "$NAME") || true
      done < <(echo "$SAMPLE")

      # If there are any names remaining, they weren't in the sample
      if echo "$NAMES" | grep '^.' > /dev/null
      then
        DBG="NAMES:\n$NAMES\n\nOUTPUT:\n$BENCH_OUT\nSAMPLE:\n$SAMPLE"
        fail "Found names which aren't in sample\n$DBG"
      fi

      mkdir "$out"
    '';
}
