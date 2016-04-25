defs: with defs; pkg:
with builtins;

let scopeResults = runScript {} ''
      set -e
      "${jq}/bin/jq" -r '.scoperesult' < "${pkg.ranTypes}" \
                                       > scopeResults.json
      "${storeResult}" scopeResults.json "$out"
    '';

    types = runScript { buildInputs = [ adb-scripts ]; } ''
      set -e
      getTypes < "${scopeResults}" > types.json
      "${storeResult}" types.json "$out"
    '';

    typeTagged = runScript { buildInputs = [ adb-scripts ]; } ''
      set -e
      tagAsts "${types}" "{}" < "${pkg.dump}" > tagged.json
      "${storeResult}" tagged.json "$out"
    '';

    count = fromJSON (parseJSON (runScript {} ''
              "${jq}/bin/jq" -r 'length' < "${typeTagged}" > "$out"
            ''));
 in testMsg (count > 0)
            "Found '${toString count}' tagged types for '${pkg.name}'"
