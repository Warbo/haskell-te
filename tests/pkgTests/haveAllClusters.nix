defs: with defs; pkg:
with builtins;

runCommand "haveAllClusters"
 {
   inherit (cluster) clusterScript;
   inherit (pkg) asts name;
   buildInputs = [ fail jq ];
 }
 ''
   for CLUSTERS in 1 2 3
   do
     export CLUSTERS
     RESULT=$("$clusterScript" < "$asts")
      FOUND=$(echo "$RESULT" | jq '.[] | .cluster')
     for NUM in $(seq 1 "$CLUSTERS")
     do
       echo "$FOUND" | grep "^$NUM$" > /dev/null ||
         fail "Clustering '$name' into '$CLUSTERS' clusters, '$NUM' was empty"
     done
   done
   echo pass > "$out"
 ''
