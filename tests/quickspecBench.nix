defs: with defs;

{
  nat-simple = runCommand "qs-nat-simple"
    {
      buildInputs = [ package ];
    }
    ''
      #!${bash}/bin/bash
      echo "Running nat-simple through quickspecBench" 1>&2
      OUTPUT=$(quickspecBench < "${../benchmarks/nat-simple.smt2}") || {
        echo "Couldn't explore nat-simple" 1>&2
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
}
