defs: with defs; pkg:
with builtins;

let arities = runScript { buildInputs = [ jq GetDeps utillinux ]; } ''
      set -e
      "${getAritiesScript}" < "${pkg.typeResults}" > arities.json
      "${storeResult}" arities.json "$out"
    '';

    arityTagged = runScript { buildInputs = [ jq GetDeps utillinux ]; } ''
      set -e
      "${tagAstsScript}" "${arities}" "{}" < "${pkg.dump}" > tagged.json
      "${storeResult}" tagged.json "$out"
    '';

    count = fromJSON (parseJSON (runScript { buildInputs = [ jq ]; } ''
              COUNT=$(jq -r 'length' < "${arityTagged}")
              if [[ -n "$COUNT" ]]
              then
                echo "$COUNT" > "$out"
              else
                echo "Didn't receive JSON array" 1>&2
                cat "${arityTagged}"             1>&2
                echo '"null"' > "$out"
              fi
            ''));
 in testMsg (if count == null
                then trace "Got null count" false
                else count > 0)
            "Found '${toString count}' tagged arities for '${pkg.name}'"
