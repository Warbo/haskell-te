#!/bin/sh
set -e

# Extract ASTs from a Cabal package

[[ "$#" -eq 0 ]] && echo "Please specify a Cabal project directory" && exit 1

DIR="$1"

PHASE="all"
[[ "$#" -gt 1 ]] && PHASE="$2"

RELBASE=$(dirname "$0")
BASE=$(readlink -f "$RELBASE")

function packageName {
    (shopt -s nullglob
     for CBL in "$DIR"/*.cabal
     do
         grep "name:" < "$CBL" | cut -d ':' -f 2 | tr -d '[:space:]'
     done)
}

function extractAsts {
    PKG=$(packageName)
    (cd "$DIR";
     nix-shell -E "with import <nixpkgs> {}; ghcWithPlugin \"$PKG\"" \
               --run "$BASE/runPlugin.sh $PHASE")
}

extractAsts
