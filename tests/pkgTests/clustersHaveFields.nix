defs: with defs; pkg:
with builtins;

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
              jq "{\"$field\": map(has(\"$field\")) | all}" < "${src."${sC}"}"
            done | jq -s '.' > "$out"
          '');

checkCluster = src: c: all (x: all (n: x."${n}") (attrNames x)) (go src c);

in all (src: all (checkCluster src) defaultClusters) [
  pkg.clustered
  pkg.preClustered
]
