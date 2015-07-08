#!/bin/sh
set -e

# Extract ASTs from a Cabal package

function packageName {
    (shopt -s nullglob
     for CBL in "$DIR"/*.cabal
     do
         grep "name:" < "$CBL" | cut -d ':' -f 2 | tr -d '[:space:]'
     done)
}

[[ "$#" -eq 0 ]] && echo "Please specify a Cabal project directory" && exit 1

DIR="$1"

RELBASE=$(dirname "$0")
BASE=$(readlink -f "$RELBASE")

PKG=$(packageName)
(cd "$DIR";
 nix-shell -E "with import <nixpkgs> {}; ghcWithPlugin \"$PKG\"" \
           --run "$BASE/runPlugin.sh")
