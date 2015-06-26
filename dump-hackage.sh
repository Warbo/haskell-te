#!/bin/sh

REL=$(dirname "$0")
ABS=$(readlink -f "$REL")
DIR=$(mktemp -d)
cd "$DIR"
cabal get "$@"
cd *
"$ABS/dump-package.sh"
cd
rm -rf "$DIR"
