#!/usr/bin/env bash

# Helpers

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
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

function testNixPackagesAugmented {
    OUTPUT=$(nixEval "<nixpkgs>")
    [[ "x$OUTPUT" = "x$BASE/nix-support" ]] ||
        fail "Nix points to '$OUTPUT' instead of '$BASE/nix-support'"
}

function testNixPackagesPristine {
    # Check that custom packages, e.g. defined in ~/.nixpkgs, don't interfere
    # with ./nix-support. These examples are from the author's configuration.
    # To avoid interference see the use of 'pristine' in nix-support/default.nix
    for QUERY in " ? warbo-utilities" \
                 " ? fs-uae" \
                 ".haskellPackages ? haskell-example"
    do
        # Check if the query matches by default
        EXPR="(import <nixpkgs> {})$QUERY"
        OUTPUT=$(nix-instantiate --show-trace --eval -E "$EXPR") ||
            fail "Failed to query default packages for '$QUERY'"

        # Skipping queries which don't even match a default config
        [[ "x$OUTPUT" = "xtrue" ]] || continue

        # Make sure the query doesn't match our augmented packages
        OUTPUT=$(nixEval "$EXPR") ||
            fail "Failed to query augmented packages for '$QUERY'"
        [[ "x$OUTPUT" = "xfalse" ]] ||
            fail "Didn't expect query '$QUERY' to match augmented packages"
    done
}

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
