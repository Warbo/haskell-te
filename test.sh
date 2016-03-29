#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq

BASE=$(dirname "$0")

function msg {
    echo -e "$1" 1>&2
}

function abort {
    # Nope out
    msg "$*"
    CODE=1
    exit 1
}

function fail {
    # Unconditional failure
    msg "FAIL $*"
    CODE=1
    return 1
}

# Test data

function buildable {
    # Test that the given package can be built normally; let alone with our
    # modifications #  \"$1\"
    BUILDABLEPKGDIR=$(getPkgDir "$1")
    msg "Attempting to build '$1' from '$BUILDABLEPKGDIR'"
    BUILDDIR=$(nix-build --show-trace --no-out-link -E \
      "(import ./defs-default.nix).build \"$BUILDABLEPKGDIR\" \"$1\"") ||
        abort "Failed to initiate build of '$1'"
    return "$(cat "$BUILDDIR/buildable")"
}

function getPkgDir {
    msg "Attempting to download '$1'"
    PKGDIR=$(nix-build --no-out-link -E \
      "with import <nixpkgs> {}; callPackage ./downloadToNix.nix {} \"$1\"") ||
        abort "Couldn't download '$1'"
    echo "$PKGDIR/source"
}

function getRawAsts {
    PKGDIR="$(getPkgDir "$1")"
    JSONDIR=$(NIX_DO_CHECK=0 nix-build --no-out-link -E \
      "with import <nixpkgs> {}; (callPackage ./defs.nix {}).dumpToNix \"$PKGDIR\"") ||
        abort "Couldn't get JSON from '$1'"
    cat "$JSONDIR/dump.json"
}

# Tests

function pkgTestGetRawAsts {
    COUNT=$(getRawAsts "$1" | jq -r "length")
    [[ "$COUNT" -gt 0 ]] ||
        fail "Couldn't get raw ASTs from '$1'"
}

# Test running infrastructure

function getTests {
    for PKG in list-extras xmonad
    do
        if buildable "$PKG" 1>&2
        then
            msg "'$PKG' is buildable, so we'll use it for tests"
            echo "pkgTestGetRawAsts $PKG"
        else
            msg "Not testing with '$PKG' as it couldn't be built"
        fi
    done
}

function traceTest {
    # Separate our stderr from the previous and give a timestamp
    msg "\n\n"
    date 1>&2

    # Always set -x to trace tests, but remember our previous setting
    OLDDEBUG=0
    [[ "$-" == *x* ]] && OLDDEBUG=1

    set -x
    export SHELLOPTS
    "$@"; PASS=$?

    # Disable -x if it wasn't set before
    [[ "$OLDDEBUG" -eq 0 ]] && set +x

    return "$PASS"
}

function runTest {
    # Log stderr in $TESTDATA. On failure, send "FAIL" and the debug
    # path to stdout
    read -ra CMD <<<"$@" # Re-parse our args to split packages from functions
    PTH=$(echo "$TESTDATA/$*" | sed 's/ /_/g')
    traceTest "${CMD[@]}" 2>> "$PTH" || {
        cat "$PTH"
        fail "$* failed"
    }
}

function runTests {
    # Overall script exit code
    CODE=0

    # Set up directories, etc.
    init

    # Handle a regex, if we've been given one
    if [[ -z "$1" ]]
    then
        TESTS=$(getTests)
    else
        TESTS=$(getTests | grep "$1")
    fi

    while read -r test
    do
        # $test is either empty, successful or we're exiting with an error
        msg "Running test '$test'"
        [[ -z "$test" ]] || runTest "$test" || CODE=1
    done < <(echo "$TESTS")

    # Remove directories, if necessary
    [[ "$CODE" -eq 0 ]] && rm -r "$TESTDATA"

    return "$CODE"
}

function init() {
    # Set the TESTDATA directory
    TESTDATA=$(mktemp -d --tmpdir 'cabal2db-test-XXXXX')
}

runTests "$1"

if [[ "$CODE" -eq 0 ]]
then
    msg "Tests passed successfully"
else
    msg "Some tests failed"
fi

exit "$CODE"
