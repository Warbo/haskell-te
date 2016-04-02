defs: with defs; pkg:

let scopeResults = runScript (withNix {}) ''
      set -e
      "${jq}/bin/jq" -r '.scoperesult' < "${testRunTypes."${pkg.name}"}" \
                                       > scopeResults.json
      "${storeResult}" scopeResults.json "$out"
    '';

    types = runScript (withNix { buildInputs = [ adb-scripts ]; }) ''
      set -e
      getTypes < "${scopeResults}" > types.json
      "${storeResult}" types.json "$out"
    '';

    count = fromJSON (parseJSON (runScript (withNix {}) ''
      "${jq}/bin/jq" -r 'length' < "${types}" > "$out"
    ''));
 in assertMsg (count > 0) "Found '${count}' types for '${pkg.name}'"
