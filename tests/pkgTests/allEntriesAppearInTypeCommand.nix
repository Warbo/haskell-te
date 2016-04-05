defs: with defs; pkg: with pkg;

parseJSON (runScript { buildInputs = [ jq ]; } ''
  set -e
  jq -c -r '.[] | .module + "." + .name' < "${preAnnotated}" |
  while read -r LINE
  do
    "${jq}/bin/jq" -r '.cmd' < "${pkg.ranTypes}" |
      grep "('$LINE)" > /dev/null || {
        echo "$LINE not in '${name}' type command" 1>&2
        exit 1
      }
  done
  echo "true" > "$out"
'')
