#!/bin/sh
set -e

REL=$(dirname "$0")
ABS=$(readlink -f "$REL")
DIR=$(mktemp -d)

(cd "$DIR";
 nix-shell -p haskellPackages.cabal-install --run "cabal get $1" > /dev/null)

for PROJECT in "$DIR"/*
do
    ./dump-package.sh "$PROJECT"
done

rm -rf "$DIR"
