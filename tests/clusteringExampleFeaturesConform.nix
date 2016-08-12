defs: with defs;
with builtins;
with lib;

let examples = mapAttrs (f: _: ./clusteringExamples + "/${f}")
                        (builtins.readDir ./clusteringExamples);
    valid    = f: _: testRun "Example '${f}' is valid"
                             null
                             { buildInputs = [ ML4HSFE ]; } ''
                   set -e
                   function featuresConform {
                     FEATURELENGTHS=$(jq -r '.[] | .features | length')
                     COUNT=$(echo "$FEATURELENGTHS" | head -n 1)
                     echo "$FEATURELENGTHS" | while read -r LINE
                     do
                       if [[ "$LINE" -ne "$COUNT" ]]
                       then
                         echo "Found '$LINE' features instead of '$COUNT'" 1>&2
                         exit 1
                       fi
                     done
                   }

                   WIDTH=30 HEIGHT=30 ml4hsfe-loop < "${f}" | featuresConform

                   exit 1
               '';
 in mapAttrs valid examples
