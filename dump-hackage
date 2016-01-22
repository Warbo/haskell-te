#!/usr/bin/env bash
set -e

DIR=$(mktemp -d)

(cd "$DIR";
 for PKG in "$@"
 do
     nix-shell --show-trace \
               -p haskellPackages.cabal-install \
               --run "cabal update; cabal get $PKG" >> /dev/stderr
 done)

(shopt -s nullglob
 for PROJECT in "$DIR"/*
 do
     echo "Dumping package $PROJECT" >> /dev/stderr
     ./dump-package.sh "$PROJECT"
 done)

rm -rf "$DIR"
