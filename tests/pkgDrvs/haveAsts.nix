defs: with defs; pkg:
with builtins;

drvFromScript { inherit (pkg) asts; } ''
  set -e

  COUNT=$(jq 'length' < "$asts")
  echo "COUNT: $COUNT" 1>&2

  if [[ "$COUNT" -eq 0 ]]
  then
    echo "Empty ASTs" 1>&2
    exit 1
  fi
  echo "Found '$COUNT' annotated ASTs" 1>&2
  echo pass > "$out"
''
