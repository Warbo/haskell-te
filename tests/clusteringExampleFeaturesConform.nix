defs: with defs;
with builtins;

let examples = map (f: ./clusteringExamples + "/${f}")
                   (builtins.attrNames (builtins.readDir ./clusteringExamples));
    valid    = f: testMsg (parseJSON (runScript {
                             buildInputs = [ jq ML4HSFE ];
                           } ''
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

                   echo "true" > "$out"
               '')) "Example '${f}' is valid";
 in testAll (map valid examples)
