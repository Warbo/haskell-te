defs: with defs; pkg:

parseJSON (runScript {} ''
  set -e
  DEPS=$(jq -cr '.[] | .dependencies | .[] | .package' < "${pkg.deps}" |
         sort -u) || {
    echo "Couldn't get packages of '${pkg.name}' dependencies" 1>&2
    exit 1
  }
  echo "$DEPS" | grep -- "-[0-9][0-9.]*$" > /dev/null && {
    echo "Deps of '${pkg.name}' have versions in package IDs:\n$DEPS" 1>&2
    exit 1
  }
  echo "true" > "$out"
'')
