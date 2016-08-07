defs: with defs; pkg:
with builtins;

drvFromScript { info = toJSON {
                  inherit (pkg) annotated dump rawDump rawAnnotated;
                };
                buildInputs = [ tests.pkgTests.haveRawAsts."${pkg.name}" ];
              } ''
  set -e
  echo "$info" 1>&2

  COUNT=$(jq 'length' < "${pkg.annotated}")
  echo "COUNT: $ANNCOUNT" 1>&2

  if [[ "$COUNT" -eq 0 ]]
  then
    echo "Empty annotated" 1>&2
    exit 1
  fi
  echo "Found '$COUNT' annotated ASTs" 1>&2
  touch "$out"
''
