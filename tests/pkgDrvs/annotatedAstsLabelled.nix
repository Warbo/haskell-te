defs: with defs; pkg:

drvFromScript
  {
    inherit (pkg) annotated;
    buildInputs = [ jq GetDeps utillinux ];
    pkgName     = pkg.name;
  }
  ''
    set -e

    jq -cr '.[] | .package' < "$annotated" | while read -r LINE
    do
      [[ "x$LINE" = "x$pkgName" ]] || {
        echo "Unlabelled: '$pkgName' '$LINE'" 1>&2
        exit 1
      }
    done
    touch "$out"
  ''
