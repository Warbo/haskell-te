{ adb-scripts, defaultClusters, explore-theories, jq, lib, ml4hs, ML4HSFE,
  parseJSON, processedPackages, recurrent-clustering, runScript, runTypes,
  storeResult, withNix }:
with builtins;
with lib;

# Attach a bunch of intermediate results to test packages, so we can check
# and cache them

let clusters         = listToAttrs (map (c: {
                                          name  = toString c;
                                          value = null;
                                        }) defaultClusters);
    testPackageNames = [ "list-extras" ];
    extend           = pkg: with pkg; pkg // rec {
      ranTypes  = runTypes dump pkg.name;

      preAnnotated = runScript
        (withNix { buildInputs = [ adb-scripts ]; })
        ''
          set -e
          annotateAsts < "${ranTypes}" > annotated.json
          "${storeResult}" annotated.json "$out"
        '';

      scopeResults = runScript
        (withNix { buildInputs = [ jq ]; })
        ''
          set -e
          jq -r '.scoperesult' < "${ranTypes}" \
                               > scopeResults.json
          "${storeResult}" scopeResults.json "$out"
        '';

      gotTypes  = runScript
        (withNix { buildInputs = [ adb-scripts ]; })
        ''
          set -e
          getTypes < "${scopeResults}" > types.json
          "${storeResult}" types.json "$out"
        '';

      typeResults = runScript (withNix {}) ''
        set -e
        "${jq}/bin/jq" -r '.result' < "${ranTypes}" \
                                    > typeResults.json
        "${storeResult}" typeResults.json "$out"
      '';

      deps = runScript
        (withNix { buildInputs = [ adb-scripts ]; })
        ''
          set -e
          getDeps < "${annotated}" > deps.json
          "${storeResult}" deps.json "$out"
        '';

      features = runScript (withNix { buildInputs = [ ML4HSFE ]; }) ''
        WIDTH=30 HEIGHT=30 ml4hsfe-loop < "${annotated}" > features.json
        "${storeResult}" features.json "$out"
      '';

      # Like 'clustered', but comes from 'features', rather than using 'cluster'
      # which acts on 'annotated'
      preClustered = mapAttrs (c: _:
        runScript (withNix { buildInputs = [ recurrent-clustering ]; })
                  ''
                    export CLUSTERS="${c}"
                    nix_recurrentClustering < "${features}" > pre-clustered.json
                    "${storeResult}" pre-clustered.json "$out"
                  '') clusters;

      formatted = mapAttrs (c: data: runScript
        (withNix { buildInputs = [ ml4hs ]; })
        ''
          set -e
          export CLUSTERS="${c}"
          "${ml4hs}/lib/ml4hs/format-exploration.sh" < "${data}" > formatted.json
          "${storeResult}" formatted.json "$out"
        '') clustered;

      # Like 'explored', but comes from 'formatted', rather than using 'ml4hs'
      # which acts on 'clustered'
      preExplored = mapAttrs (c: data: runScript
        (withNix { buildInputs = [ explore-theories ]; })
        ''
          set -e

          function shallow {
            grep -v "^Depth" || true # Prevent set -e choking on empty input
          }

          export CLUSTERS="${c}"
          explore-theories < "${data}" | shallow > equations.json
          "${storeResult}" equations.json "$out"
      '') formatted;
    };
in listToAttrs (map (n: { name  = n;
                          value = extend processedPackages."${n}"; })
                    testPackageNames)
