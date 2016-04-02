defs: with defs; pkg:

let rawData = runTypes pkg.dump pkg.name;

    scopeResults = runScript (withNix {}) ''
      set -e
      "${jq}/bin/jq" -r '.scoperesult' < "${rawData}" > scopeResults.json
      "${storeResult}" scopeResults.json "$out"
    '';

    types = runScript (withNix { buildInputs = [ adb-scripts ]; }) ''
      set -e
      getTypes < "${scopeResults}" > types.json
      "${storeResult}" types.json "$out"
    '';

    typeTagged = runScript (withNix { buildInputs = [ adb-scripts ]; }) ''
      set -e
      tagAsts "${types}" "{}" < "${pkg.dump}" > tagged.json
      "${storeResult}" tagged.json "$out"
    '';

    count = fromJSON (parseJSON (runScript {} ''
              "${jq}/bin/jq" -r 'length' < "${typeTagged}" > "$out"
            ''));
 in assertMsg (count > 0) "Found '${count}' tagged types for '${pkg.name}'"
