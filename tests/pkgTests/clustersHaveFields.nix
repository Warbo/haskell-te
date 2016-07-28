defs: with defs; pkg:
with builtins;
with lib;

let

go = src: c:
  let sC = toString c;
   in parseJSON
        (runScript
          { buildInputs = [ jq ]; }
          ''
            set -e
            for field in arity name module type package ast features cluster \
                         quickspecable
            do
              jq "{\"$field\": map(has(\"$field\")) | all}" < "${src.${sC}}"
            done | jq -s '.' > "$out"
          '');

checkCluster = src: c:
  testWrap (concatMap (x: map (n: testMsg x."${n}"
                                  "Clusters of ${pkg.name} have field '${n}'")
                              (attrNames x))
                      (go src c))
           "${pkg.name} cluster ${toString c} has fields";

in testWrap (map (src: testWrap (map (checkCluster src) defaultClusters)
                                "Checking cluster")
                 [
                   pkg.clustered
                   pkg.preClustered
                 ])
            "Clusters have fields"
