defs: with defs; pkg:
with builtins;

drvFromScript { inherit (pkg) annotated; } ''
  set -e

  COUNT=$(jq 'length' < "$annotated")
  echo "COUNT: $ANNCOUNT" 1>&2

  if [[ "$COUNT" -eq 0 ]]
  then
    echo "Empty annotated" 1>&2
    exit 1
  fi
  echo "Found '$COUNT' annotated ASTs" 1>&2
  touch "$out"
''
