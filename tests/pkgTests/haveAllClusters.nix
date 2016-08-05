defs: with defs; pkg:
with builtins;

let check = c:
      let sC    = toString c;
          stdin = readFile pkg.clustered."${sC}";
          have  = parseJSON (runScript { buildInputs = [ jq ]; } ''
            set -e
            FOUND=$(jq '.[] | .cluster' < "${pkg.clustered.${sC}}")
            for NUM in $(seq 1 "${sC}")
            do
              echo "$FOUND" | grep "^$NUM$" > /dev/null || {
                echo "Clustering '${pkg.name}' into '${sC}' clusters, '$NUM' was empty" 1>&2
                echo "false" > "$out"
              }
            done
            echo "true" > "$out"
          '');
          result = if stdin == ""
                      then trace "Got no stdin" false
                      else have;
       in testDbg result "Have clusters for ${sC}" {
            inherit c sC stdin;
            inherit (pkg) clustered;
          };
 in testAll (map check defaultClusters)
