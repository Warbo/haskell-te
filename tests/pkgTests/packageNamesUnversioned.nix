defs: with defs; pkg:

drvFromScript {} ''
  set -e

  function assertNoVersions {
    if grep -- "-[0-9][0-9.]*$" > /dev/null
    then
      echo "Versions found in package names of $1${pkg.name}" 1>&2
      exit 1
    fi
  }

  F="${pkg.annotated}"
  [[ -e "$F" ]] || {
    echo "Couldn't find file '$F'" 1>&2
    exit 1
  }
  jq -rc '.[] | .package'                       < "$F" |
    assertNoVersions "'$1'"

  jq -rc '.[] | .dependencies | .[] | .package' < "$F" |
    assertNoVersions "dependencies of '$1'"

  touch "$out"
''
