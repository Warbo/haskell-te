{ annotateAstsScript, defaultClusters, drvFromScript, GetDeps, getDepsScript,
  getTypesScript, jq, lib, ML4HSFE, nixRecurrentClusteringScript, parseJSON,
  processPackages, runScript, runTypes, runWeka, storeResult, utillinux }:
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

      preAnnotated = drvFromScript
        {
          inherit ranTypes;
          buildInputs = [ GetDeps ];
        }
        ''
          set -e
          cat "$ranTypes" 1>&2
          "${annotateAstsScript}" < "$ranTypes" > "$out"
        '';

      scopeResults = runScript { buildInputs = [ jq ]; } ''
        set -e
        jq -r '.scoperesult' < "${ranTypes}" \
                             > scopeResults.json
        "${storeResult}" scopeResults.json "$out"
      '';

      gotTypes = runScript { buildInputs = [ GetDeps ]; } ''
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

      deps = runScript { buildInputs = [ GetDeps ]; } ''
        set -e
        "${getDepsScript}" < "${annotated}" > deps.json
        "${storeResult}" deps.json "$out"
      '';

      features = runScript { buildInputs = [ ML4HSFE ]; } ''
        echo "Turning annotated '${pkg.name}' at '${annotated}' into features" 1>&2
        WIDTH=30 HEIGHT=30 ml4hsfe-loop < "${annotated}" > features.json
        "${storeResult}" features.json "$out"
      '';
    };

in

assert isAttrs processedPackages;
assert all (n: elem n (attrNames processedPackages)) testPackageNames;

listToAttrs (map (n: { name  = n;
                       value = extend processedPackages."${n}"; })
                 testPackageNames)
