defs: with defs;

let examples = map (f: ./clusteringExamples + "/${f}")
                   (builtins.attrNames (builtins.readDir ./clusteringExamples));
    valid    = f: testMsg (parseJSON (runScript {} ''
                 set -e
                 "${jq}/bin/jq" '.' < "${f}" > /dev/null
                 echo "true" > "$out"
               '')) "Example '${f}' is valid";
 in all valid examples
