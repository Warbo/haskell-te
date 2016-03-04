#!/usr/bin/env bash

# Helpers

BASE=$(dirname "$(readlink -f "$0")")

function fail {
    echo -e "FAIL: $1" >> /dev/stderr
    exit 1
}

function nixPath {
    # Get the path to 'nixpkgs'
    REAL=$(nix-instantiate --eval -E '<nixpkgs>') || fail "Couldn't invoke Nix"

    # Alias <nixpkgs> to <real> and use nix-support in place of <nixpkgs>
    [[ -d "$BASE/nix-support" ]] || fail "Couldn't find nix-support in '$BASE'"
    echo "nixpkgs=$BASE/nix-support:real=$REAL:$NIX_PATH"
}

function nixEval {
    NIX_PATH="$(nixPath)" nix-instantiate --show-trace --eval -E "$1"
}

function nixPackages {
    cat <<EOF
mlspec-bench
explore-theories
EOF
}

# Tests

function testNixPackagesAugmented {
    OUTPUT=$(nixEval "<nixpkgs>")
    [[ "x$OUTPUT" = "x$BASE/nix-support" ]] ||
        fail "Nix points to '$OUTPUT' instead of '$BASE/nix-support'"
}

function testNixPackagesPristine {
    # If you have any custom packages, e.g. in ~/.nixpkgs, you can add them here
    # to check that they don't interfere with ./nix-support
    for QUERY in " ? warbo-utilities" " ? fs-uae" ".haskellPackages ? haskell-example"
    do
        # Check if the given attribute is available by default
        EXPR="(import <nixpkgs> {})$QUERY"
        OUTPUT=$(nix-instantiate --show-trace --eval -E "$EXPR") ||
            fail "Failed to query default packages for '$QUERY'"

        [[ "x$OUTPUT" = "xtrue" ]] || {
            echo "Skipping query '$QUERY'" >> /dev/stderr
            continue
        }

        # Make sure the attribute isn't interfering with our augmented packages
        OUTPUT=$(nixEval "$EXPR") ||
            fail "Failed to query augmented packages for '$QUERY'"
        [[ "x$OUTPUT" = "xfalse" ]] ||
            fail "Didn't expect query '$QUERY' to match augmented packages"
    done
}

function testNixPackagesAvailable {
    while read -r ATTR
    do
        TYPE=$(nixEval "builtins.typeOf (import <nixpkgs> {}).$ATTR") ||
            fail "Couldn't get type of '$ATTR'"
        [[ "x$TYPE" = "x\"set\"" ]] || fail "'$ATTR' is a '$TYPE', should be a set"
    done < <(nixPackages)
}

function testNixPackagesUsable {
    while read -r ATTR
    do
        NIX_PATH="$(nixPath)" nix-shell --show-trace --run true \
                              -p "(import <nixpkgs> {}).$ATTR" --run true ||
            fail "Couldn't build environment containing '$ATTR'"
    done < <(nixPackages)
}

function testBenchmarks {
    NIX_PATH="$NEW_PATH" "$BASE/bench-test.sh"
}

# Test invocation

testNixPackagesAugmented
testNixPackagesPristine
testNixPackagesAvailable
testNixPackagesUsable
#testBenchmarks

exit

# Accumulate results, so we can repeat them after each package (to avoid
# trudging through compiler output)
RESULT=""

# Test each package we care about (dependencies will take care of themselves)
while read -r pkg
do
    RESULT="${RESULT}Testing $pkg: "
    if ./one.sh "$pkg"
    then
        RESULT="$RESULT PASS\n"
    else
        RESULT="$RESULT FAIL\n"
    fi
    echo -e "Results so far:\n$RESULT"
done < <(grep "call = " < default.nix | sed -e 's/^[ ]*\([^ ]*\).*/\1/g')
