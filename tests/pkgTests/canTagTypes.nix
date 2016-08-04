defs: with defs; pkg:
with builtins;

let scopeResults = runScript {} ''
      set -e
      "${jq}/bin/jq" -r '.scoperesult' < "${pkg.ranTypes}" \
                                       > scopeResults.json
      "${storeResult}" scopeResults.json "$out"
    '';

    types = runScript { buildInputs = [ jq GetDeps utillinux ]; } ''
      set -e
      "${getTypesScript}" < "${scopeResults}" > types.json
      "${storeResult}" types.json "$out"
    '';

    typeTagged = runScript { buildInputs = [ jq GetDeps utillinux ]; } ''
      set -e
      "${tagAstsScript}" "${types}" "{}" < "${pkg.dump}" > tagged.json
      "${storeResult}" tagged.json "$out"
    '';

    count = fromJSON (parseJSON (runScript { buildInputs = [ jq ]; } ''
              COUNT=$(jq -r 'length' < "${typeTagged}")
              if [[ -n "$COUNT" ]]
              then
                echo "$COUNT" > "$out"
              else
                echo "Didn't receive JSON array" 1>&2
                cat "${typeTagged}"              1>&2
                echo '"null"' > "$out"
              fi
            ''));
 in testMsg (if count == null
                then trace "Got null count" false
                else count > 0)
            "Found '${toString count}' tagged types for '${pkg.name}'"
