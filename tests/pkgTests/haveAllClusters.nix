defs: with defs; pkg:
with builtins;

let check = c: let sC = toString c; in parseJSON (runScript {
      buildInputs = [ jq ];
    } ''
      set -e
      FOUND=$(jq '.[] | .cluster' < "${pkg.clustered."${sC}"}")
      for NUM in $(seq 1 "${sC}")
      do
        echo "$FOUND" | grep "^''${NUM}$" > /dev/null || {
          echo "Clustering '${pkg.name}' into '${sC}' clusters, '$NUM' was empty" 1>&2
          exit 1
        }
      done
      echo "true" > "$out"
    '');
 in all check defaultClusters
