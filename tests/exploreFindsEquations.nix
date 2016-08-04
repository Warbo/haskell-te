defs: with defs; with builtins;

let

path   = toString ./exploreTheoriesExamples;

files  = map (f: "${path}/${f}") (attrNames (readDir path));

foundEquations = f:
  let env = { buildInputs = explore.extractedEnv { inherit f; }; };
      cmd = ''
        set -e
        set -o pipefail

        echo "Exploring '${f}'" 1>&2
        OUTPUT=$("${explore.explore-theories f}" < "${f}" 2>&1) || {
          echo -e "Failed to explore '${f}', output follows:\n$OUTPUT\nEND" 1>&2
          exit 2
        }

        if echo "$OUTPUT" | grep "No clusters found"
        then
          echo "No clusters found by MLSpec (did it receive any input?)" 1>&2
          exit 3
        fi

        if echo "$OUTPUT" | grep "^{" > /dev/null
        then
          echo "Found equations for '${f}'" 1>&2
          echo "true" > "$out"
        else
          echo -e "Couldn't find any equations in output of '${f}':\n$OUTPUT" 1>&2
          echo "false" > "$out"
        fi
      '';
   in parseJSON (runScript env cmd);

foundAny = any foundEquations files;

in testMsg foundAny "Equations found"
