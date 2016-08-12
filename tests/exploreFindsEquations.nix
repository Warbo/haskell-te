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
          if [[ -e sout ]]
          then
            echo -e "\n\nstdout:\n\n" 1>&2
            cat sout                  1>&2
          else
            echo "No stdout produced" 1>&2
          fi

          if [[ -e serr ]]
          then
            echo -e "\n\nstderr:\n\n" 1>&2
            cat serr                  1>&2
          else
            echo "No stderr produced" 1>&2
          fi

          echo  "COUNT: $COUNT"  1>&2
        }
        trap finish EXIT

        echo "Exploring '$f'" 1>&2
        "${explore.explore-theories}" < "$f" 1> sout 2> serr || {
          echo -e "Failed to explore '$f'"
          exit 2
        }

        if grep "No clusters found" < serr
        then
          echo "No clusters found by MLSpec (did it receive any input?)" 1>&2
          exit 3
        fi

        COUNT=$(jq 'length' < sout)

        if [[ "$COUNT" -eq 0 ]]
        then
          echo -e "Couldn't find any equations in output of '$f'" 1>&2
          exit 0
        else
          echo "Found '$COUNT' equations for '$f'" 1>&2
          exit 0
        fi
      '';
   in testRun "Testing ${name}" null env cmd;

in mapAttrs foundEquations files
