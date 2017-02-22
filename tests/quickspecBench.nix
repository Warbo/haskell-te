defs: with defs;

with rec {
  maxSecs = 300;

  fail = msg: ''{ echo -e "${msg}" 1>&2; exit 1; }'';

  testFile = name: path: runCommand "qs-${name}"
    {
      buildInputs = [ jq package ];
    }
    ''
      #!${bash}/bin/bash
      export MAX_SECS="${maxSecs}"

      echo "Running ${name} through quickspecBench" 1>&2
      OUTPUT=$(quickspecBench < "${path}") || {
        echo "Couldn't explore ${name}" 1>&2
        exit 1
      }

      T=$(echo "$OUTPUT" |
          jq 'has("cmd") and has("info") and has("results")') || {
        echo -e "Couldn't parse output\nSTART\n$OUTPUT\nEND" 1>&2
        exit 1
      }

      [[ "x$T" = "xtrue" ]] || {
        echo -e "Required fields missing:\n$OUTPUT" 1>&2
        exit 1
      }

      echo "Pass" > "$out"
    '';
};
{
  list-full  = testFile "list-full"  ../benchmarks/list-full.smt2;
  nat-full   = testFile "nat-full"   ../benchmarks/nat-full.smt2;
  nat-simple = testFile "nat-simple" ../benchmarks/nat-simple.smt2;

  sample-tip = runCommand "sample-tip"
    {
      buildInputs = [ jq package tipBenchmarks.tools ];
    }
    ''
      #!/usr/bin/env bash
      set -e
      export MAX_SECS="${maxSecs}"

      BENCH_OUT=$(SAMPLE_SIZES="5" quickspecBench)

      # Get all the constant symbols in all equations
      STDOUTS=$(echo "$BENCH_OUT" | jq -r '.results | .[] | .stdout') ||
        ${fail "Couldn't get stdouts\n\n$BENCH_OUT"}

      OUTPUTS=$(while read -r F
                do
                  cat "$F"
                  echo ""
                done < <(echo "$STDOUTS")) ||
        ${fail "Couldn't concat stdouts\n\n$BENCH_OUT\n\n$STDOUTS"}

      EQS=$(echo "$OUTPUTS" | grep -v '^Depth') ||
        ${fail "Couldn't get eqs\n\n$BENCH_OUT\n\n$OUTPUTS"}

      NAMES=$(echo "$EQS" |
              jq -r 'getpath(paths(type == "object" and .role == "constant")) |
                     .symbol' |
              sort -u) || ${fail "Couldn't get names\n\n$BENCH_OUT\n\n$EQS"}
      SAMPLE=$(choose_sample 5 1)

      # Remove any names which appear in the sample
      while read -r NAME
      do
        NAMES=$(echo "$NAMES" | grep -vFx "$NAME") || true
      done < <(echo "$SAMPLE")

      # If there are any names remaining, they weren't in the sample
      if echo "$NAMES" | grep '^.' > /dev/null
      then
        echo "Found names which aren't in sample" 1>&2
        echo -e "NAMES:\n$NAMES\n\nOUTPUT:\n$BENCH_OUT\nSAMPLE:\n$SAMPLE" 1>&2
        exit 1
      fi

      echo "Passed" > "$out"
    '';
}
