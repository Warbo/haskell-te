#!/bin/bash
set -e

REL=$(dirname "$0")
ABS=$(readlink -f "$REL")
DIR=$(mktemp -d)

(cd "$DIR";
 nix-shell --show-trace -p haskellPackages.cabal-install --run "cabal get $1" > /dev/stderr)

(shopt -s nullglob
 for PROJECT in "$DIR"/*
 do
     echo "Dumping package $PROJECT" > /dev/stderr
     ./dump-package.sh "$PROJECT"
 done)

rm -rf "$DIR"
