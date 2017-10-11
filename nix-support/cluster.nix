{ annotated, bash, fail, haskellPackages,jq, lib, ML4HSFE, runCommand, runWeka,
  testData, unpack, withDeps, wrap }:

with builtins;
with lib;
with rec {
  clusterScript-untested = wrap {
    name   = "cluster";
    paths  = [ bash ML4HSFE runWeka ];
    script = ''
      #!/usr/bin/env bash
      set -e

      [[ -n "$WIDTH"  ]] ||  WIDTH=30
      [[ -n "$HEIGHT" ]] || HEIGHT=30
      export WIDTH
      export HEIGHT
      ml4hsfe-outer-loop
    '';
  };

  test = attr: pkg:
    with rec {
      asts      = getAttr attr (testData.asts {});
      clustered = runCommand "cluster"
        {
          inherit asts;
          cmd = clusterScript-untested;
        }
        ''
          "$cmd" < "$asts" > "$out"
        '';

      clustersHaveFields = runCommand "clustersHaveFields-for-${pkg.name}"
        {
          inherit clustered;
          buildInputs = [ fail jq ];
        }
        ''
          set -e
          jq -e 'length | . > 0' < "$clustered" || fail "No clusters"

          for field in arity name module type package ast features cluster \
                       quickspecable
          do
            jq -e "map(has(\"$field\")) | all" < "$clustered"
          done

          mkdir "$out"
        '';

      featuresConform = runCommand "features-conform-${attr}"
        {
          inherit clustered;
          buildInputs = [ fail jq ];
        }
        ''
          set -e

          FEATURELENGTHS=$(jq -r '.[] | .features | length' < "$clustered")
          COUNT=$(echo "$FEATURELENGTHS" | head -n 1)
          echo "$FEATURELENGTHS" | while read -r LINE
          do
            [[ "$LINE" -eq "$COUNT" ]] ||
              fail "Found '$LINE' features, was expecting '$COUNT'"
          done
          mkdir "$out"
        '';

      haveAllClusters = runCommand "haveAllClusters-${attr}"
        {
          inherit asts;
          inherit (pkg) name;
          buildInputs = [ fail jq ];
          cluster     = clusterScript-untested;
        }
        ''
          for CLUSTERS in 1 2 3
          do
            export CLUSTERS
            RESULT=$("$cluster" < "$asts")
            FOUND=$(echo "$RESULT" | jq '.[] | .cluster')
            for NUM in $(seq 1 "$CLUSTERS")
            do
              echo "$FOUND" | grep "^$NUM$" > /dev/null || fail \
                "Clustering '$name' into '$CLUSTERS' clusters, '$NUM' was empty"
            done
          done
          mkdir "$out"
        '';
    };
    [ clustersHaveFields featuresConform haveAllClusters ];

  tests = concatLists (attrValues (mapAttrs test testData.haskellDrvs));
};

withDeps tests clusterScript-untested
