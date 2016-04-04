defs: with defs; pkg:

let go = src: c: let sC = toString c; in parseJSON (runScript {
      buildInputs = [ jq ];
    } ''
      set -e
      for field in arity name module type package ast features cluster quickspecable
      do
        jq "{\"$field\": map(has(\"$field\")) | all}" < "${src."${sC}"}"
      done | jq -s '.' > "$out"
    '');
    check = src: c: all (x: all (n: x."${n}") (attrNames x)) (go src c);
 in all (src: all (check src) defaultClusters) [pkg.clustered pkg.preClustered]
