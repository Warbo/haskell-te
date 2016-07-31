{ annotateAstsScript, defaultClusters, getDeps, getDepsScript,
  getTypesScript, jq, lib, ml4hs, ML4HSFE, nixRecurrentClusteringScript,
  parseJSON, processPackages, runScript, runTypes, runWeka, storeResult,
  utillinux }:
with builtins;
with lib;

# Attach a bunch of intermediate results to test packages, so we can check
# and cache them

let clusters         = listToAttrs (map (c: {
                                          name  = toString c;
                                          value = null;
                                        }) defaultClusters);

    testPackageNames  = [ "list-extras" ];

    processedPackages = processPackages { quick = true; };

    extend            = pkg: with pkg; pkg // rec {
      ranTypes  = runTypes dump pkg {};

      preAnnotated = runScript { buildInputs = [ jq getDeps utillinux ]; } ''
        set -e
        "${annotateAstsScript}" < "${ranTypes}" > annotated.json
        "${storeResult}" annotated.json "$out"
      '';

      scopeResults = runScript { buildInputs = [ jq ]; } ''
        set -e
        jq -r '.scoperesult' < "${ranTypes}" \
                             > scopeResults.json
        "${storeResult}" scopeResults.json "$out"
      '';

      gotTypes = runScript { buildInputs = [ jq getDeps utillinux ]; } ''
        set -e
        "${getTypesScript}" < "${scopeResults}" > types.json
        "${storeResult}" types.json "$out"
      '';

      typeResults = runScript {} ''
        set -e
        "${jq}/bin/jq" -r '.result' < "${ranTypes}" \
                                    > typeResults.json
        "${storeResult}" typeResults.json "$out"
      '';

      deps = runScript { buildInputs = [ jq getDeps utillinux ]; } ''
        set -e
        "${getDepsScript}" < "${annotated}" > deps.json
        "${storeResult}" deps.json "$out"
      '';

      features = runScript { buildInputs = [ ML4HSFE ]; } ''
        WIDTH=30 HEIGHT=30 ml4hsfe-loop < "${annotated}" > features.json
        "${storeResult}" features.json "$out"
      '';

      # Like 'clustered', but comes from 'features', rather than using 'cluster'
      # which acts on 'annotated'
      preClustered = mapAttrs (c: _:
        runScript { buildInputs = [ order-deps ML4HSFE nix jq runWeka ]; } ''
          export CLUSTERS="${c}"
          "${nixRecurrentClusteringScript}" < "${features}" > pre-clustered.json
          "${storeResult}" pre-clustered.json "$out"
        '') clusters;
    };

in

assert isAttrs processedPackages;
assert all (n: elem n (attrNames processedPackages)) testPackageNames;

listToAttrs (map (n: { name  = n;
                       value = extend processedPackages."${n}"; })
                 testPackageNames)
