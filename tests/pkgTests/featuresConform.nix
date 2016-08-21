defs: with defs; pkg:

with builtins;
with lib;

let checkCluster = cluster: drvFromScript { inherit cluster;
                                            buildInputs = [ jq ML4HSFE ]; } ''
      set -e

      FEATURELENGTHS=$(jq -r '.[] | .features | length' < "$cluster")
      COUNT=$(echo "$FEATURELENGTHS" | head -n 1)
      echo "$FEATURELENGTHS" | while read -r LINE
      do
        if [[ "$LINE" -eq "$COUNT" ]]
        then
          echo "Found '$LINE' features, as expected" 1>&2
        else
          echo "Found '$LINE' features, was expecting '$COUNT'" 1>&2
          exit 1
        fi
      done

      touch "$out"
    '';
 in mapAttrs (_: checkCluster) pkg.clustered
