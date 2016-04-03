defs: with defs;

let examples = map (f: ./clusteringExamples + "/${f}")
                   (builtins.attrNames (builtins.readDir ./clusteringExamples));
                   count = f: parseJSON (runScript { buildInputs = [ jq ML4HSFE ]; } ''
                             set -e
                             #ENAME=$(basename "${f}")
                             WIDTH=30 HEIGHT=30 ml4hsfe-loop < "${f}" |
                               grep -c "^" > "$out"
                           '');
    valid    = f: assertMsg (fromJSON (count f) > 0)
                            "Checking for features in '${f}'";
 in all valid examples
