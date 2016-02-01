#! /usr/bin/env nix-shell
#! nix-shell -i bash -p bash jq

function abort {
    # Nope out
    [[ "$#" -eq 0 ]] || echo "$*" >> /dev/stderr
    exit 1
}

function fail {
    # Unconditional failure
    [[ "$#" -eq 0 ]] || echo "FAIL $*"
    CODE=1
    return 1
}

# Test data

function getRawJson {
    # Takes a package name, dumps its ASTs into $TESTDATA
    F="$TESTDATA/$1.rawjson"
    [[ ! -e "$F" ]] &&
        NOFORMAT="true" ./dump-hackage "$1" > "$F"
    cat "$F"
}

function getRawAsts {
    # Takes a package name, dumps its ASTs into $TESTDATA
    F="$TESTDATA/$1.rawasts"
    [[ ! -e "$F" ]] &&
        ./dump-hackage "$1" > "$F"
    cat "$F"
}

# Tests

function pkgTestGetRawJson {
    getRawJson "$1" | grep -c "^" > /dev/null ||
        fail "Couldn't get raw JSON from '$1'"
}

function pkgTestGetRawAsts {
    COUNT=$(getRawAsts "$1" | jq -r "length")
    [[ "$COUNT" -gt 0 ]] ||
        fail "Couldn't get raw ASTs from '$1'"
}

# Test running infrastructure

function getFunctions {
    # Get a list of the functions in this script
    declare -F | cut -d ' ' -f 3-
}

function getPkgTests {
    # Get a list of test functions which require a package
    getFunctions | grep '^pkgTest'
}

function getTests {
    # Get a list of all test functions
    getFunctions | grep '^test'

    # Apply each package test to each package
    while read -r pkg
    do
        while read -r test
        do
            echo "$test $pkg"
        done < <(getPkgTests)
    done < <(getTestPkgs)
}

function getTestPkgs {
    # A list of packages to test with
    cat <<EOF
list-extras
EOF
}

function traceTest {
    # Separate our stderr from the previous and give a timestamp
    echo -e "\n\n" >> /dev/stderr
    date           >> /dev/stderr

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
    # Log stderr in $TESTDATA/debug. On failure, send "FAIL" and the debug
    # path to stdout
    read -ra CMD <<<"$@" # Re-parse our args to split packages from functions
    PTH=$(echo "$TESTDATA/debug/$*" | sed 's/ /_/g')
    traceTest "${CMD[@]}" 2>> "$PTH" || fail "$* failed, see $PTH"
}

function runTests {
    # Overall script exit code
    CODE=0

    # Handle a regex, if we've been given one
    if [[ -z "$1" ]]
    then
        TESTS=$(getTests)
    else
        TESTS=$(getTests | grep "$1")
    fi

    # Set up directories, etc.
    init

    while read -r test
    do
        # $test is either empty, successful or we're exiting with an error
        [[ -z "$test" ]] || runTest "$test" || CODE=1
    done < <(echo "$TESTS")

    # Remove directories, if necessary
    cleanup

    return "$CODE"
}

function init() {
    # Set the TESTDATA directory
    if [[ -n "$CABAL2DBTESTDIR" ]]
    then
        TMPDIR=""
        TESTDATA="$CABAL2DBTESTDIR/test-data"
    else
        TMPDIR=$(mktemp -d -t 'cabal2db-test-XXXXX')
        TESTDATA="$TMPDIR/test-data"
    fi

    [[ -n "$TESTDATA" ]] ||
        abort "Error with test data dir"

    INITIAL=$(echo "$TESTDATA" | cut -c 1)
    [[ "x$INITIAL" = "x/" ]] ||
        abort "Test data dir '$TESTDATA' must be absolute"

    echo "Attempting to create test data dir '$TESTDATA'" >> /dev/stderr
    mkdir -p "$TESTDATA/debug" ||
        abort "Couldn't make test data dir '$TESTDATA'"
}

function cleanup() {
    # Remove the TESTDATA directory, if we've been asked
    [[ -n "$CABAL2DBCLEANUP" ]] && {
        echo "Removing test data dir '$TESTDATA', as instructed" >> /dev/stderr
        rm -r "$TESTDATA"
        [[ -n "$TMPDIR" ]] && {
            echo "Removing temp directory '$TMPDIR' as well" >> /dev/stderr
            rmdir "$TMPDIR"
        }
    }
}

runTests "$1"
