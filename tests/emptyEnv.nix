defs: with defs;

# The contents of extra-haskell-packages should be available, even with no
# ENVIRONMENT_PACKAGES given
let result = runScript {} ''
  set -e
  while read -r PKG
  do
    unset ENVIRONMENT_PACKAGES
    "${explore.build-env}" ghc-pkg list "$PKG" || {
      echo "Extra package '$PKG' wasn't found with empty environment" 1>&2
      exit 2
    }
  done < <("${explore.extra-haskell-packages}")
  echo "true" > "$out"
'';

in testMsg (parseJSON result) "Default env contains extra-haskell-packages"
