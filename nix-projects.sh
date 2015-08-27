#!/usr/bin/env bash

source common.sh

# FIXME: Temporary hack until bug #63 is fixed in QuickCheck
QCFIX=$(readlink -f ./quickcheck-fix.nix)
EXTRA=$(cat <<EOF
    cp "$QCFIX" ./quickcheck-fix.nix
    sed -i 's@callPackage f {}@callPackage f { QuickCheck = import ./quickcheck-fix.nix; }@g' shell.nix
EOF
)

# Use cabal2nix to give every Cabal project a Nix file
# We run the loop inside nix-shell to save setup/teardown time
PROJECTS=$(cat)
nix-shell -p cabal2nix -p bash --run "bash" <<EOF
source common.sh
CODE=0
while read PROJECT
do
    cd "\$PROJECT"
    cabal2nix --shell ./. > shell.nix || CODE=1
    $EXTRA
done < <(echo "$PROJECTS")
exit "\$CODE"
EOF
