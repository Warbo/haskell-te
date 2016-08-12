defs: with defs; with builtins;
with lib;

let

path   = toString ../exploreTheoriesExamples;

files  = mapAttrs (f: _: "${path}/${f}") (readDir path);

foundEquations = name: f:
  let env = { buildInputs = explore.extractedEnv { inherit f; };
              inherit f; };
      cmd = ''
        set -e
        set -o pipefail
        set -x

        function finish {
          echo "OUTPUT: $OUTPUT" 1>&2
          echo  "COUNT: $COUNT"  1>&2
        }
        trap finish EXIT


        echo "Exploring '$f'" 1>&2
        OUTPUT=$("${explore.explore-theories f}" < "$f" 2>&1) || {
          echo -e "Failed to explore '$f', output follows:\n$OUTPUT\nEND" 1>&2
          exit 2
        }

        if echo "$OUTPUT" | grep "No clusters found"
        then
          echo "No clusters found by MLSpec (did it receive any input?)" 1>&2
          exit 3
        fi

        COUNT=$(echo "$OUTPUT" | jq 'length')

        if [[ "$COUNT" -eq 0 ]]
        then
          echo -e "Couldn't find any equations in output of '$f':\n$OUTPUT" 1>&2
          exit 0
        else
          echo "Found '$COUNT' equations for '$f'" 1>&2
          exit 0
        fi
      '';
   in testRun "Testing ${name}" null env cmd;

in mapAttrs foundEquations files
