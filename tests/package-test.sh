#!/usr/bin/env bash

# Run test suites of our package submodules

shopt -s nullglob
BASE=$(dirname "$(dirname "$(readlink -f "$0")")")

# Helper functions

function msg {
    echo -e "$1" >> /dev/stderr
}

function fail {
    msg "FAIL: $*"
    exit 1
}

function inTmpDir {
    DIR=$(mktemp -d --tmpdir "haskell-te-testXXXXX")
    pushd "$DIR" > /dev/null
    "$@"
    CODE="$?"
    popd > /dev/null
    rm -rf "$DIR"
    return "$CODE"
}

# Test functions

function testShellScripts {
    CLONEDIR="test_script_clone_dir"

    # Look for packages with a "test.sh" script
    for TESTSCRIPT in "$BASE/packages"/*/test.sh
    do
        # Clone the package into our temporary directory, so we can test a
        # pristine version without cluttering up the filesystem
        PKGDIR=$(dirname "$TESTSCRIPT")
        [[ -d "$CLONEDIR" ]] && rm -rf "$CLONEDIR"
        git clone "$PKGDIR" "$CLONEDIR"
        pushd "$CLONEDIR" > /dev/null

        # Run the tests
        msg "Running '$PWD/test.sh' cloned from '$TESTSCRIPT'"
        ./test.sh || fail "'$PWD/test.sh' exited with an error"
        popd > /dev/null
    done
}

# Test invocation

function runTests {
    while read -r TEST
    do
        msg "Running '$TEST'"
        "$TEST"
        msg "PASS: $TEST"
    done < <(declare -F | cut -d ' ' -f 3 | grep "^test")
}

inTmpDir runTests
