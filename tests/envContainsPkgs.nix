defs: with defs;

# Append more and more Haskell packages to ENVIRONMENT_PACKAGES
drvFromScript { buildInputs = explore.exploreEnv; } ''
  set -e
  PKGS=""
  for NEWPKG in text containers parsec aeson
  do
    PKGS=$(echo -e "$PKGS\n$NEWPKG")

    ENVIRONMENT_PACKAGES="$PKGS" "${explore.checkHsEnv []}" || {
      echo "checkHsEnv passed for '$PKGS'" 1>&2
      exit 2
    }
  done

  touch "$out"
''
