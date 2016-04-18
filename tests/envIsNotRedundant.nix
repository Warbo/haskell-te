defs: with defs;

let result = runScript {} ''
  set -e
  echo "Checking we don't build a new nix-shell when packages are available" 1>&2

  function nixception {
    # For use by testEnvIsNotRedundant. Requires particular variables to be
    # initialised. We only keep it separate to avoid heredoc annoyances.
    # shellcheck disable=SC2086
    nix-shell --show-trace -p "$GHCPKG" $EXTRA --run bash <<EOF
  echo "BEGIN INNER SHELL" 1>&2
  for PKG in $HLINE
  do
    ENVIRONMENT_PACKAGES="$EXTRAH" "${explore.build-env}" ghc-pkg list "\$PKG" |
    grep "\$PKG" > /dev/null || {
      echo "Didn't find '\$PKG' in environment" 1>&2
      exit 1
    }
  done
  EOF
  }

  # build-env adds some 'extra' packages on to those we give it; they must be
  # available too
  EXTRA=$("${explore.extra-packages}")
  EXTRAH=$("${explore.extra-haskell-packages}" | grep "^.")
  HLINE=$(echo "$EXTRAH" | tr '\n' ' ')
  PREFIXED=$(echo "$EXTRAH"| sed -e 's/^/h./g')
  GHCPKG="haskellPackages.ghcWithPackages (h: [$PREFIXED])"

  echo "Building an environment for each Haskell package, inside a nix-shell" 1>&2
  echo "which already has them all available" 1>&2
  OUTPUT=$(nixception 2>&1) || {
    echo "Inner environment is missing packages" 1>&2
    exit 2
  }

  echo "Making sure build-env ran" 1>&2
  echo "$OUTPUT" | grep "BEGIN INNER SHELL" > /dev/null || {
    echo "Inner shell didn't seem to run" 1>&2
    exit 3
  }

  echo "Making sure build-env didn't create a new Nix environment" 1>&2
  echo "$OUTPUT" | grep -A 9999 "BEGIN INNER SHELL" | grep "building path" && {
    echo "Built Nix environment when it wasn't needed" 1>&2
    exit 4
  }

  echo "build-env didn't make unnecessary environment" 1>&2
  echo "true" > "$out"
'';

in testMsg (parseJSON result) "Environment doesn't get rebuilt inappropriately"
