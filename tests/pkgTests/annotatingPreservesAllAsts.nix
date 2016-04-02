defs: with defs; pkg:

let rawData   = testRunTypes."${pkg.name}";
    annotated = testAnnotated."${pkg.name}";
    result = parseJSON (runScript { buildInputs = [ jq ]; } ''
      set -e
      jq -c '.asts | .[]' < "${rawData}" | while read -r LINE
      do
        NAME=$(echo "$LINE" | jq -r '.name')
        MOD=$( echo "$LINE" | jq -r '.module')
        PKG=$( echo "$LINE" | jq -r '.package')
        PRED=".name == \"$NAME\" and .module == \"$MOD\" and .package == \"$PKG\""
        COUNT=$(jq "map(select($PRED)) | length" < "${annotated}")
        [[ "$COUNT" -eq 1 ]] || {
          echo "$PKG:$MOD.$NAME was in raw data but not ASTs" 1>&2
          exit 1
        }
      done
      echo "true" > "$out"
    '');
 in assertMsg result "All raw ASTs of '${pkg.name}' remain after annotation"
