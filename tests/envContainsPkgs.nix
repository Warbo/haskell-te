defs: with defs;

# Append more and more Haskell packages to ENVIRONMENT_PACKAGES
let result = runScript { buildInputs = explore.exploreEnv; } ''
  set -e
  PKGS=""
  for NEWPKG in text containers parsec aeson
  do
    PKGS=$(echo -e "$PKGS\n$NEWPKG")

    # For each package we're giving to build-env, check it becomes available
    # by calling ghc-pkg
    for PKG in $PKGS
    do
      OUTPUT=$(ENVIRONMENT_PACKAGES="$PKGS" "${explore.build-env}" ghc-pkg list "$PKG") || {
        echo "Couldn't run ghc-pkg in build-env for '$PKG' in '$PKGS'" 1>&2
        exit 2
      }
      echo "$OUTPUT" | grep "$PKG" > /dev/null || {
        echo "Didn't find package '$PKG' in ghc-pkg output '$OUTPUT'" 1>&2
        exit 3
      }
      echo "Package '$PKG' was found in the environment" 1>&2
    done
  done
  echo "true" > "$out"
'';

in testMsg (parseJSON result) "Packages found in environment"
