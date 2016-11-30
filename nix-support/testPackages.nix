{ annotateAstsScript, defaultClusters, drvFromScript, GetDeps, getDepsScript,
  lib, processPackages, runScript, runTypes, runWeka,
  storeResult }:
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

      scopeResults = runScript {} ''
        set -e
        jq -r '.scoperesult' < "${ranTypes}" \
                             > scopeResults.json
        "${storeResult}" scopeResults.json "$out"
      '';

      typeResults = runScript {} ''
        set -e
        jq -r '.result' < "${ranTypes}" > typeResults.json
        "${storeResult}" typeResults.json "$out"
      '';

      deps = runScript { buildInputs = [ GetDeps ]; } ''
        set -e
        "${getDepsScript}" < "${annotated}" > deps.json
        "${storeResult}" deps.json "$out"
      '';
    };

in

assert isAttrs processedPackages;
assert all (n: elem n (attrNames processedPackages)) testPackageNames;

listToAttrs (map (n: { name  = n;
                       value = extend processedPackages."${n}"; })
                 testPackageNames)
