#!/bin/sh

REL=$(dirname "$0")
ABS=$(readlink -f "$REL")
DIR=$(mktemp -d)

(cd "$DIR";
 nix-shell -p haskellPackages.cabal-install --run "cabal get $1" > /dev/null)

cd *
for PROJECT in "$DIR"/*
do
    "$ABS/dump-package.sh" "$PROJECT"
done
cd
rm -rf "$DIR"
