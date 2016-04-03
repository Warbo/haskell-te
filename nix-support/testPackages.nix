{ adb-scripts, jq, processedPackages, runScript, runTypes, storeResult,
  withNix }:
with builtins;

# Attach a bunch of intermediate results to test packages, so we can check
# and cache them

let testPackageNames = [ "list-extras" ];
    extend           = pkg: with pkg; pkg // rec {
      ranTypes  = runTypes dump pkg.name;

      annotated = runScript
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
    };
in listToAttrs (map (n: { name  = n;
                          value = extend processedPackages."${n}"; })
                    testPackageNames)
