{ writeScript }:
with builtins;

# Extract ASTs from a Cabal package
let

# Runs AstPlugin.
#
# This script makes the following assumptions:
#  - The path to a Cabal project is given as an argument
#  - All of the project's dependencies are in the database of ghc-pkg
#  - AstPlugin is also in the database of ghc-pkg
runAstPlugin = writeScript "runAstPlugin" ''
  #!/usr/bin/env bash
  set -e

  function packageMissing {
    for P in "$PKG" AstPlugin
    do
      "$1" list "$P" | grep '(no packages)' > /dev/null && return 0
    done
    return 1
  }

  function getAsts {
    OPTIONS="-package-db=$GHC_PKG -package AstPlugin -fplugin=AstPlugin.Plugin"

    # NOTE: GHC plugins write to stderr
    cabal --ghc-options="$OPTIONS" build 1> "$TEMPDIR/stdout" 2> "$TEMPDIR/stderr"

    # Send all JSON lines to stdout
    cat "$TEMPDIR/stdout" "$TEMPDIR/stderr" | grep    "^{"      || true

    # Send everything else to stderr
    cat "$TEMPDIR/stdout" "$TEMPDIR/stderr" | grep -v "^{" 1>&2 || true
  }

  cd "$1"

  GHC_PKG=""
  if packageMissing "ghc-pkg"
  then
    # Not found in the DB. Maybe broken nix-shell nesting, try elsewhere in PATH
    while read -r DIR
    do
      # Ignore entries which don't contain ghc-pkg
      [[ -e "$DIR/ghc-pkg" ]] || continue

      # Ignore ghc-pkg entries which don't contain AstPlugin or $PKG
      packageMissing "$DIR/ghc-pkg" && continue

      # If we're here, we've found a ghc-pkg with AstPlugin and $PKG
      GHC_PKG=$("$DIR/ghc-pkg" list | head -n 1 | tr -d ':')
      break
    done < <(echo "$PATH" | tr ':' '\n' | grep ghc)

    if [[ -z "$GHC_PKG" ]]
    then
      echo "Couldn't find ghc-pkg for AstPlugin & '$PKG'" 1>&2
      exit 1
    fi
  else
    GHC_PKG=$(ghc-pkg list | head -n 1 | tr -d ':')
  fi

  cabal configure --package-db="$GHC_PKG" 1>&2

  getAsts | jq -c ". + {package: \"$PKG\"}" | jq -s '.'
'';

dump-package-name = writeScript "dump-package-name" ''
  #!/usr/bin/env bash
  set -e
  echo "Looking for .cabal files in '$1'" 1>&2

  shopt -s nullglob
  for CBL in "$1"/*.cabal
  # */
  do
    echo "Found '$CBL' in '$1'" 1>&2
    NAME=$(grep -i "name[ ]*:" < "$CBL" | cut -d ':' -f 2 | tr -d '[:space:]')
    echo "Project name is '$NAME'" 1>&2
    echo "$NAME"
    exit 0
  done

  echo "Couldn't find name of package in '$1'" 1>&2
  exit 1
'';

in writeScript "dump-package" ''
     #!/usr/bin/env bash
     set -e

     [[ -n "$DIR" ]] || DIR="$1"
     [[ -n "$DIR" ]] || {
       echo "Please provide a package directory, either as argument or DIR" 1>&2
       exit 3
     }

     [[ -d "$DIR" ]] || {
       echo "Directory '$DIR' not found" 1>&2
       exit 1
     }

     PKG=$("${dump-package-name}" "$DIR")
     export PKG

     ENV=$(echo "with import <nixpkgs> {}; import \"${./ghcWithPlugin.nix}\" \"$PKG\"") || {
       echo "Unable to get package environment; aborting" 1>&2
       exit 2
     }

     nix-shell --show-trace \
               -E "$ENV" \
               --run "'${runAstPlugin}' '$DIR'"
   ''
