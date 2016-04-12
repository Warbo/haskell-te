defs: with defs; pkg:
with builtins;

let check = c: let sC = toString c; in parseJSON (runScript {
        buildInputs = [ jq ];
    } ''
      export CLUSTERS="${sC}"
      if jq '.[] | .tocluster' < "${pkg.preClustered."${sC}"}" | grep "false" > /dev/null
      then
         echo "Clustering '${pkg.name}' into '${sC}' missed things" 1>&2
         exit 1
      fi
      echo "true" > "$out"
    '');
 in all check defaultClusters
