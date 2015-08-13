#!/usr/bin/env bash

source common.sh

# Use cabal2nix to give every Cabal project a Nix file
# We run the loop inside nix-shell to save setup/teardown time
PROJECTS=$(cat)
nix-shell -p cabal2nix -p bash --run "bash" <<EOF
CODE=0
while read PROJECT
do
    cd "\$PROJECT"
    cabal2nix --shell ./. > shell.nix || CODE=1
    cd ..
done < <(echo "$PROJECTS")
exit "\$CODE"
EOF
