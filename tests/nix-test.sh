#!/usr/bin/env bash

# Helpers

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")

# shellcheck source=../scripts/common.sh
source "$BASE/scripts/common.sh"

function fail {
    echo -e "FAIL: $1" >> /dev/stderr
    exit 1
}

function nixPath {
    "$BASE/nix-support/nixPath.sh"
}

function nixEval {
    NIX_PATH="$(nixPath)" nix-instantiate --show-trace --eval -E "$1"
}

function nixPackages {
    cat <<EOF
explore-theories
mlspec
mlspec-bench
haskellPackages.ArbitraryHaskell
haskellPackages.mlspec
haskellPackages.mlspec-bench
haskellPackages.mlspec-helper
haskellPackages.nix-eval
haskellPackages.runtime-arbitrary
EOF
}

# Tests

function testNixPackagesAvailable {
    while read -r ATTR
    do
        EXPR="builtins.typeOf (import <nixpkgs> {}).$ATTR"
        echo "Attempting to evaluate '$EXPR'..." >> /dev/stderr
        TYPE=$(nixEval "$EXPR") ||
            fail "Couldn't get type of '$ATTR'"
        [[ "x$TYPE" = "x\"set\"" ]] || fail "'$ATTR' is a '$TYPE', should be a set"
    done < <(nixPackages)
}

function testNixPackagesUsable {
    # As an extra bonus, any test suites included in a package should get run as
    # part of the build process
    while read -r ATTR
    do
        echo "Building environment for '$ATTR'" >> /dev/stderr
        NIX_PATH="$(nixPath)" nix-shell --show-trace --run true \
                              -p "(import <nixpkgs> {}).$ATTR" --run true ||
            fail "Couldn't build environment containing '$ATTR'"
    done < <(nixPackages)
}

# Test invocation

testNixPackagesAugmented
testNixPackagesPristine
testNixPackagesAvailable
testNixPackagesUsable

echo "Nix tests passed (for more info, see messages above)"
