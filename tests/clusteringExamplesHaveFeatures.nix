defs: with defs;
with builtins;

let examples = map (f: ./clusteringExamples + "/${f}")
                   (builtins.attrNames (builtins.readDir ./clusteringExamples));
                   count = f: parseJSON (runScript { buildInputs = [ jq ML4HSFE ]; } ''
                             set -e
                             WIDTH=30 HEIGHT=30 ml4hsfe-loop < "${f}" |
                               grep -c "^" > "$out"
                           '');
    valid    = f: testMsg (fromJSON (count f) > 0)
                          "Checking for features in '${f}'";
 in testAll (map valid examples)
