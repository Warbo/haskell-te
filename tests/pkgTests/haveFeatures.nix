defs: with defs; pkg:
with builtins;

drvFromScript { buildInputs = [ ML4HSFE ]; } ''
  set -e
  COUNT=$(grep -c "^" < "${pkg.features}") || true

  if [[ "$COUNT" -eq 0 ]]
  then
    echo "Got no features" 1>&2
    exit 1
  fi
  echo "Found '$COUNT' features" 1>&2
''
