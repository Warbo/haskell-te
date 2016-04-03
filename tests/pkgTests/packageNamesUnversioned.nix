defs: with defs; pkg:

parseJSON (runScript {} ''
  set -e

  function assertNoVersions {
    if grep -- "-[0-9][0-9.]*$" > /dev/null
    then
         echo "Versions found in package names of $1${pkg.name}" 1>&2
         exit 1
    fi
  }


  jq -rc '.[] | .package'                       < "{pkg.annotated}" |
    assertNoVersions "'$1'"

  jq -rc '.[] | .dependencies | .[] | .package' < "{pkg.annotated}" |
    assertNoVersions "dependencies of '$1'"

  echo "true" > "$out"
'')
