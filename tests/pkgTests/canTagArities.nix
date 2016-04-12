defs: with defs; pkg:
with builtins;

let arities = runScript (withNix { buildInputs = [ adb-scripts ]; }) ''
      set -e
      getArities < "${pkg.typeResults}" > arities.json
      "${storeResult}" arities.json "$out"
    '';

    arityTagged = runScript (withNix { buildInputs = [ adb-scripts ]; }) ''
      set -e
      tagAsts "${arities}" "{}" < "${pkg.dump}" > tagged.json
      "${storeResult}" tagged.json "$out"
    '';

    count = fromJSON (parseJSON (runScript {} ''
              "${jq}/bin/jq" -r 'length' < "${arityTagged}" > "$out"
            ''));
 in testMsg (count > 0)
            "Found '${toString count}' tagged arities for '${pkg.name}'"
