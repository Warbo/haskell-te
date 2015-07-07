#!/bin/sh
set -e
set -x

REL=$(dirname "$0")
ABS=$(readlink -f "$REL")
DIR=$(mktemp -d)
PHASE="all"
[[ "$#" -gt 1 ]] && PHASE="$2"

(cd "$DIR";
 nix-shell -p haskellPackages.cabal-install --run "cabal get $1" > /dev/null)

for PROJECT in "$DIR"/*
do
    ./dump-package.sh "$PROJECT" "$PHASE"
done

rm -rf "$DIR"
