defs: with defs; pkg:

parseJSON (runScript { buildInputs = [ jq getDeps utillinux ]; } ''
  set -e
  jq -c '.[] | .package'  < "${pkg.preAnnotated}" | while read -r LINE
  do
    [[ "x$LINE" = "x\"${pkg.name}\"" ]] || {
      echo "Unlabelled: '${pkg.name}' '$LINE'" 1>&2
      exit 1
    }
  done
  echo "true" > "$out"
'')
