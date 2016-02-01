#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq haskellPackages.ShellCheck cabal2db annotatedb recurrent-clustering
shopt -s nullglob

BASE=$(dirname "$0")

# Simple test suite for ML4HS:
#  - Given no arguments, all tests will be run
#  - Given a regex as argument, only matching tests will be run
#  - Only failures are reported; no failure == success
#  - Intermediate results are cached in test-data/
#  - stderr and execution traces are written to test-data/debug
#  - There is no cache invalidation, so just delete test-data as needed
#  - Functions with names beginning with "test" will be called automatically
#  - Functions with names beginning with "testPkg" will be called automatically
#    with a selection of package names as their first argument

# Assertion functions

function fail {
    # Unconditional failure
    [[ "$#" -eq 0 ]] || echo "FAIL $*"
    CODE=1
    return 1
}

# Functions to get data; expensive calls should cache in test-data/

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
    #xmonad
    #pandoc
    #git-annex
    #hakyll
    #egison
    #lens
    #warp
    #conduit
    #ghc-mod
    #shelly
    #http-conduit
    #yesod-core
}

function getRawAsts {
    F="test-data/$1.rawasts"
    [[ ! -e "$F" ]] &&
        dump-hackage "$1" > "$F"
    cat "$F"
}

function getAsts {
    F="test-data/$1.asts"
    [[ ! -e "$F" ]] &&
        getRawAsts "$1" | annotateDb "$1" > "$F"
    cat "$F"
}

function getFeatures {
    F="test-data/$1.features"
    [[ ! -e "$F" ]] &&
        getAsts "$1" | extractFeatures > "$F"
    cat "$F"
}

function getClusters {
    [[ -z "$CLUSTERS" ]] && CLUSTERS=4
    export CLUSTERS
    F="test-data/$1.clusters.$CLUSTERS"
    [[ ! -e "$F" ]] &&
        getFeatures "$1" | nix_recurrentClustering > "$F"
    cat "$F"
}

function getEquations {
    mkdir -p test-data/projects
    [[ -z "$CLUSTERS" ]] && CLUSTERS=4
    F="test-data/$1.rawEquations.$CLUSTERS"
    if [[ ! -e "$F" ]]
    then
        getClusters "$1" | "$BASE/run-exploration.sh" > "$F"
    fi
    cat "$F"
}

# Tests requiring a package as argument

function countCommas {
    tr -dc ',' | wc -c
}

function pkgTestEquations {
    for CLUSTERS in 1 2 3 5 7 11
    do
        echo "'$CLUSTERS' CLUSTERS FOR '$1'" >> /dev/stderr
        getEquations "$1" || fail "Couldn't get equations for '$1'"
    done
}

# Tests requiring no arguments

function testShellCheck {
    SCERR=0
    IGNORE=(
        -e SC1008 # #!/usr/bin/env nix-shell is OK
        -e SC2016 # "jq '$foo'" is OK
        -e SC2001 # Complex sed can't be replaced by bash builtins
    )
    for file in *.sh
    do
        shellcheck -s bash "${IGNORE[@]}" "$file" || SCERR=1
    done
    return "$SCERR"
}

function testShebangs {
    ERR=0
    for file in *.sh
    do
        SHEBANGS=$(grep "^#!" < "$file")
        if echo "$SHEBANGS" | grep "/bin/sh" > /dev/null
        then
            fail "$file won't work on Debian. Use #!/usr/bin/env bash"
            ERR=1
        fi
        if echo "$SHEBANGS" | grep "/bin/bash" > /dev/null
        then
            fail "$file won't work on NixOS. Use #!/usr/bin/env bash"
            ERR=1
        fi
    done
    return "$ERR"
}

function testStderr {
    ERR=0
    for file in *.sh
    do
        if grep "[^>]>[ ]*/dev/stderr" < "$file" > /dev/null
        then
            fail "$file overwrites stderr instead of appending"
            ERR=1
        fi
    done
    return "$ERR"
}

# Test invocation

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
    # Log stderr in test-data/debug. On failure, send "FAIL" and the debug
    # path to stdout
    read -ra CMD <<<"$@" # Re-parse our args to split packages from functions
    PTH=$(echo "test-data/debug/$*" | sed 's/ /_/g')
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

    while read -r test
    do
        # $test is either empty, successful or we're exiting with an error
        [[ -z "$test" ]] || runTest "$test" || CODE=1
    done < <(echo "$TESTS")
    return "$CODE"
}

mkdir -p test-data/debug
runTests "$1"
