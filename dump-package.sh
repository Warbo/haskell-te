#!/usr/bin/env bash
set -e

# Extract ASTs from a Cabal package

function packageName {
    echo "Looking for .cabal files in '$DIR'" >> /dev/stderr
    (shopt -s nullglob
     for CBL in "$DIR"/*.cabal
     do
         echo "Found '$CBL' in '$DIR'"  >> /dev/stderr
         NAME=$(grep -i "name[ ]*:" < "$CBL" | cut -d ':' -f 2 | tr -d '[:space:]')
         echo "Project name is '$NAME'" >> /dev/stderr
         echo "$NAME"
     done)
}

function runPlugin {
    nix-shell --show-trace \
              -E "with import <nixpkgs> {}; import ./ghcWithPlugin.nix \"$PKG\"" \
              --run "./runPlugin.sh $DIR"
}

function format {
    # Set NOFORMAT to avoid calling jq, eg. for testing
    if [[ -z $NOFORMAT ]]
    then
        jq -c ". + {package: \"$PKG\"}" | jq -s '.'
    else
        cat
    fi
}

[[ "$#" -eq 0 ]] && echo "Please specify a Cabal project directory" && exit 1

DIR="$1"
PKG=$(packageName)

runPlugin | format
