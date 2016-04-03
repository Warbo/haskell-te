defs: with defs; pkg:

parseJSON (runScript { buildInputs = [ jq ]; } ''
  set -e
  jq -c '.asts | .[]' < "${pkg.ranTypes}" | while read -r LINE
  do
    NAME=$(echo "$LINE" | jq -r '.name')
    MOD=$( echo "$LINE" | jq -r '.module')
    PKG=$( echo "$LINE" | jq -r '.package')
    PRED=".name == \"$NAME\" and .module == \"$MOD\" and .package == \"$PKG\""
    COUNT=$(jq "map(select($PRED)) | length" < "${pkg.annotated}")
    [[ "$COUNT" -eq 1 ]] || {
      echo "$PKG:$MOD.$NAME was in raw data but not ASTs" 1>&2
      exit 1
    }
  done
  echo "true" > "$out"
'')
