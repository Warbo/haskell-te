#!/usr/bin/env bash

BASE=$(dirname "$0")

DIR=$(mktemp -dt "haskell-te-XXXXX")

echo "Fetching packages to '$DIR'" >> /dev/stderr

pushd "$DIR" > /dev/null
while read -r PKG
do
    cabal get "$PKG"
done < <("$BASE/shufflePackages.sh")
popd > /dev/null
