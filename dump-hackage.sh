#!/usr/bin/env bash
set -e

REL=$(dirname "$0")
ABS=$(readlink -f "$REL")
DIR=$(mktemp -d)

(cd "$DIR";
 for PKG in "$@"
 do
     nix-shell --show-trace -p haskellPackages.cabal-install --run "cabal get $PKG" > /dev/stderr
 done)

(shopt -s nullglob
 for PROJECT in "$DIR"/*
 do
     echo "Dumping package $PROJECT" > /dev/stderr
     ./dump-package.sh "$PROJECT"
 done)

rm -rf "$DIR"
