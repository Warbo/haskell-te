defs: with defs; pkg:

let rawData = runTypes pkg.dump pkg.name;

    annotated = runScript (withNix { buildInputs = [ adb-scripts ]; }) ''
      set -e
      annotateAsts < "${rawData}" > annotated.json
      "${storeResult}" annotated.json "$out"
    '';

    count = fromJSON (parseJSON (runScript (withNix {}) ''
      "${jq}/bin/jq" -r 'length' < "${annotated}" > "$out"
    ''));
 in assertMsg (count > 0) "Found '${count}' annotated ASTs for '${pkg.name}'"
