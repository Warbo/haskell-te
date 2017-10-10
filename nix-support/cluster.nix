{ annotated, bash, fail, haskellPackages,jq, lib, ML4HSFE, runCommand, runWeka,
  testPackageNames, unpack, withDeps, wrap }:

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

  test = attr:
    with rec {
      pkg       = getAttr attr haskellPackages;
      asts      = annotated { pkgDir = unpack pkg.src; };
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
    };
    [ clustersHaveFields featuresConform ];

  tests = concatMap test testPackageNames;
};

withDeps tests clusterScript-untested
