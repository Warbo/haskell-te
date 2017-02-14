defs: with defs;

with {
  testFile = name: path: runCommand "qs-${name}"
    {
      buildInputs = [ jq package ];
    }
    ''
      #!${bash}/bin/bash
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
}
