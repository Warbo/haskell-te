defs: with defs; pkg:
with builtins;

drvFromScript { buildInputs = [ ML4HSFE jq ]; } ''
  set -e
  echo -e "Features:"       1>&2
  cat     "${pkg.features}" 1>&2

  COUNT=$(jq 'length' < "${pkg.features}")

  echo "COUNT: $COUNT" 1>&2

  if [[ "$COUNT" -eq 0 ]]
  then
    echo "Got no features" 1>&2
    exit 1
  fi
  echo "Found '$COUNT' features" 1>&2
  touch "$out"
''
