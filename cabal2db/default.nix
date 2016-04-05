{ stdenv, haskellPackages, nix, gnutar, jq, lib, runCommand, writeScript,
  doCheck ? true }:

rec {
  runScript       = import ./runScript.nix       {
                      inherit lib writeScript runCommand;
                    };

  importDir       = import ./importDir.nix       {
                      inherit lib;
                    };

  withNix         = env: let existing = if env ? buildInputs
                                           then env.buildInputs
                                           else [];
                          in env // {
                               # Required for calling nix recursively
                               buildInputs = existing ++ [ nix ];
                               NIX_REMOTE  = "daemon";
                               NIX_PATH    = builtins.getEnv "NIX_PATH";
                               # Allows ~/.nixpkgs/config.nix to help debugging
                               USER_HOME   = builtins.getEnv "HOME";
                             };

  dump-package-env = writeScript "dump-package-env" ''
    #!/usr/bin/env bash
    set -e

    [[ "$#" -gt 0 ]] || {
      echo "dump-package-env needs a Cabal project directory" 1>&2
      exit 1
    }

    [[ -d "$1" ]] || {
      echo "Directory '$1' not found" 1>&2
      exit 1
    }

    DIR="$1"
    PKG=$("${dump-package-name}" "$DIR")

    echo "with import <nixpkgs> {}; import \"${ghcWithPlugin}\" \"$PKG\""
  '';

  ghcWithPlugin = ./ghcWithPlugin.nix;

  dump-format = ./dump-format;

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

  # Extracts ASTs from a Cabal package
  dump-package = writeScript "dump-package" ''
    #!/usr/bin/env bash
    set -e

    [[ -n "$DIR" ]] || DIR="$1"
    [[ -n "$DIR" ]] || {
      echo "Please provide a package directory, either as argument or DIR" 1>&2
      exit 3
    }

    ENV=$("${dump-package-env}" "$DIR") || {
      echo "Unable to get package environment; aborting" 1>&2
      exit 2
    }

    nix-shell --show-trace \
              -E "$ENV" \
              --run "'${runAstPlugin}' '$DIR'"
  '';

  runAstPlugin = writeScript "runAstPlugin" ''
    #!/usr/bin/env bash

    # Runs AstPlugin.
    #
    # This script makes the following assumptions:
    #  - The path to a Cabal project is given as an argument
    #  - All of the project's dependencies are in the database of ghc-pkg
    #  - AstPlugin is also in the database of ghc-pkg

    # The dependency requirements can be satisfied by running in nix-shell

    set -e

    function getAsts {
        RESULT=$(build)
        { echo "$RESULT" | grep -v "^{" 1>&2; } || true
          echo "$RESULT" | grep    "^{"
    }

    function build {

        # NOTE: We swap stderr (2) and stdout (1) via a temporary fd (3), since GHC
        # plugins write to stderr
        cabal --ghc-options="$OPTIONS" build 3>&2 2>&1 1>&3
    }

    function packageMissing {
        for P in "$PKG_NAME" AstPlugin
        do
            "$1" list "$P" | grep '(no packages)' > /dev/null && return 0
        done
        return 1
    }

    [[ "$#" -eq 0 ]] && echo "runAstPlugin needs a directory" && exit 1

    PKG_NAME=$("${dump-package-name}" "$1") || {
        echo "Couldn't get package name from '$1'" 1>&2
        exit 1
    }

    cd "$1"

    # Override pkg db to get project's dependencies and AstPlugin
    GHC_PKG=""
    if packageMissing "ghc-pkg"
    then
        # Not found in the DB. Maybe broken nix-shell nesting, try elsewhere in PATH
        while read -r DIR
        do
            # Ignore entries which don't contain ghc-pkg
            [[ -e "$DIR/ghc-pkg" ]] || continue

            # Ignore ghc-pkg entries which don't contain AstPlugin or $PKG_NAME
            packageMissing "$DIR/ghc-pkg" && continue

            # If we're here, we've found a ghc-pkg with AstPlugin and $PKG_NAME
            GHC_PKG=$("$DIR/ghc-pkg" list | head -n 1 | tr -d ':')
            break
        done < <(echo "$PATH" | tr ':' '\n' | grep ghc)

        if [[ -z "$GHC_PKG" ]]
        then
            echo "Couldn't find ghc-pkg for AstPlugin & '$PKG_NAME'" 1>&2
            exit 1
        fi
    else
        GHC_PKG=$(ghc-pkg list | head -n 1 | tr -d ':')
    fi

    OPTIONS="-package-db=$GHC_PKG -package AstPlugin -fplugin=AstPlugin.Plugin"

    [[ -n "$SKIP_CABAL_CONFIG" ]] ||
        cabal configure --package-db="$GHC_PKG" 1>&2

    getAsts | "${dump-format}" "$1"
  '';
}
