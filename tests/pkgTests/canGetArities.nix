defs: with defs; pkg:
with builtins;

let typeResults = runScript {} ''
      set -e
      "${jq}/bin/jq" -r '.result' < "${pkg.ranTypes}" \
                                  > typeResults.json
      "${storeResult}" typeResults.json "$out"
    '';

    arities = runScript { buildInputs = [ jq GetDeps utillinux ]; } ''
      set -e
      "${getAritiesScript}" < "${typeResults}" > arities.json
      "${storeResult}" arities.json "$out"
    '';

    count = fromJSON (parseJSON (runScript {} ''
              "${jq}/bin/jq" -r 'length' < "${arities}" > "$out"
            ''));
 in testDbg (count > 0) "Found arities for '${pkg.name}'"
            {
              inherit count arities typeResults getAritiesScript;
              inherit (pkg) ranTypes;
            }
