#!/bin/bash
set -e

# Extract ASTs from a Cabal package

function packageName {
    echo "Looking for .cabal files in '$DIR'" > /dev/stderr
    (shopt -s nullglob
     for CBL in "$DIR"/*.cabal
     do
         echo "Found '$CBL' in '$DIR'"  > /dev/stderr
         NAME=$(grep -i "name[ ]*:" < "$CBL" | cut -d ':' -f 2 | tr -d '[:space:]')
         echo "Project name is '$NAME'" > /dev/stderr
         echo "$NAME"
     done)
}

[[ "$#" -eq 0 ]] && echo "Please specify a Cabal project directory" && exit 1

DIR="$1"

RELBASE=$(dirname "$0")
BASE=$(readlink -f "$RELBASE")

PKG=$(packageName)
(cd "$DIR";
 nix-shell --show-trace \
           -E "with import <nixpkgs> {}; ghcWithPlugin \"$PKG\"" \
           --run "$BASE/runPlugin.sh")
