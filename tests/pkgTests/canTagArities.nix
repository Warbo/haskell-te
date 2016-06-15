defs: with defs; pkg:
with builtins;

let arities = runScript { buildInputs = [ adb-scripts ]; } ''
      set -e
      "${getAritiesScript}" < "${pkg.typeResults}" > arities.json
      "${storeResult}" arities.json "$out"
    '';

    arityTagged = runScript { buildInputs = [ adb-scripts ]; } ''
      set -e
      "${tagAstsScript}" "${arities}" "{}" < "${pkg.dump}" > tagged.json
      "${storeResult}" tagged.json "$out"
    '';

    count = fromJSON (parseJSON (runScript {} ''
              "${jq}/bin/jq" -r 'length' < "${arityTagged}" > "$out"
            ''));
 in testMsg (count > 0)
            "Found '${toString count}' tagged arities for '${pkg.name}'"
