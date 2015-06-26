#!/bin/sh

REL=$(dirname "$0")
ABS=$(readlink -f "$REL")
DIR=$(mktemp -d)
cd "$DIR"
nix-shell -p haskellPackages.cabal-install --run "cabal get $1"
cd *
"$ABS/dump-package.sh"
cd
rm -rf "$DIR"
