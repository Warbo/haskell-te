#! /usr/bin/env nix-shell
#! nix-shell -i bash -p adb-scripts jq ML4HSFE

BASE=$(dirname "$0")

function msg {
    echo -e "$1" 1>&2
}

# Assertion functions

function fail {
    # Unconditional failure
    msg "FAIL $*"
    CODE=1
    return 1
}

function assertNotEmpty {
    # Fails if stdin is empty
    COUNT=$(grep -c "^")
    [[ "$COUNT" -gt 0 ]] || fail "$1"
}

function assertNoVersions {
    grep -- '-[0-9][0-9.]*$' > /dev/null &&
        fail "Versions found in package names of $1"
}

# Look up tests from the environment

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
        runTraced getRawAsts "$pkg" > /dev/null || {
            msg "Can't get raw ASTs for '$pkg', skipping"
            msg "Flaky package or bug in Cabal2DB:"
            cat "$PTH" 1>&2
            continue
        }
        runTraced getAsts "$pkg" > /dev/null || {
            msg "Can't get ASTs for '$pkg', skipping"
            msg "Flaky package or bug in annotatedb:"
            cat "$PTH" 1>&2
            continue
        }
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
    return
    regex-tdfa
    xmonad
    hakyll
}

# Data generators

function getRawAsts {
    F="test-data/$1.rawasts"
    [[ ! -e "$F" ]] && {
        # Hide errors, but log them via set -x debugging
        OUTPUT=$( { nix-shell -p cabal2db --run "dump-hackage '$1'" > "$F"; } 2>&1 ) || {
            fail "Couldn't get raw ASTs for '$1' ($(echo "$OUTPUT" | wc -l) lines of output)"
            return 1
        }
    }
    [[ -n "$(cat "$F")" ]] || {
        fail "Raw ASTs for '$1' are empty"
        return 1
    }
    cat "$F"
}

function getAsts {
    getRawAsts "$1" > /dev/null || {
        fail "Can't get ASTs for '$1' as raw ASTs don't work"
        return 1
    }

    F="test-data/$1.asts"
    [[ ! -e "$F" ]] && {
        getRawAsts "$1" | annotateDb "$1" > "$F" || {
            fail "Failed to annotate ASTs for '$1'"
            return 1
        }
    }
    [[ -n "$(cat "$F")" ]] || {
        fail "Got empty output for '$1' ASTs"
        return 1
    }
    cat "$F"
}

function getFeatures {
    F="test-data/$1.features"
    [[ ! -e "$F" ]] && {
        getAsts "$1" | WIDTH=30 HEIGHT=30 ml4hsfe-loop > "$F"
    }
    cat "$F"
}

function exampleFeatures {
    ENAME=$(basename "$1")
    F="test-data/$ENAME.features"
    [[ ! -e "$F" ]] && {
        # Disable tracing as it takes up a LOT of space
        OLDDEBUG=0
        [[ "$-" == *x* ]] && OLDDEBUG=1

        set +x
        WIDTH=30 HEIGHT=30 ml4hsfe-loop < "$1" > "$F"

        # Enable -x if it was set before
        [[ "$OLDDEBUG" -eq 0 ]] || set -x
    }
    cat "$F"
}

function getClusters {
    [[ -n "$CLUSTERS" ]] || fail "No CLUSTERS for getClusters"
    export CLUSTERS
    F="test-data/$1.clusters.$CLUSTERS"
    [[ ! -e "$F" ]] &&
        getFeatures "$1" | "$BASE/nix_recurrentClustering" > "$F"
    cat "$F"
}

function getEndToEnd {
    [[ -n "$CLUSTERS" ]] || fail "No CLUSTERS for getEndToEnd"
    export CLUSTERS
    F="test-data/$1.endtoend.$CLUSTERS"
    [[ ! -e "$F" ]] && {
        # Disable tracing as it takes up a LOT of space
        OLDDEBUG=0
        [[ "$-" == *x* ]] && OLDDEBUG=1

        set +x
        getAsts "$1" | "$BASE/cluster" > "$F"

        # Enable -x if it was set before
        [[ "$OLDDEBUG" -eq 0 ]] || set -x
    }
    cat "$F"
}

function getExampleFiles {
    while read -r FILE
    do
        readlink -f "$FILE"
    done < <(find examples -type f)
}

# Feature extraction tests

# Clustering tests; each is tested with the feature extraction output and via
# the top-level "cluster" command, on test packages and examples

function clusterNums {
    # The number of clusters to test with. Since it's expensive, we use the same
    # numbers each time, so the caches can be re-used.
    cat <<EOF
1
2
11
EOF
}

###

function haveAllClusters {
    while read -r CLUSTERS
    do
        FOUND=$("$2" "$1" | jq '.[] | .cluster')
        for NUM in $(seq 1 "$CLUSTERS")
        do
            echo "$FOUND" | grep "^${NUM}$" > /dev/null ||
                fail "Clustering '$1' into '$CLUSTERS' clusters, '$NUM' was empty"
        done
    done < <(clusterNums)
}

function pkgTestHaveAllClusters {
    haveAllClusters "$1" getClusters
}

function pkgTestHaveAllEndToEnd {
    haveAllClusters "$1" getEndToEnd
}

###

function clusterFields {
    while read -r CLUSTERS
    do
        for field in arity name module type package ast features cluster quickspecable
        do
            RESULT=$("$2" "$1" | jq "map(has(\"$field\")) | all")
            [[ "x$RESULT" = "xtrue" ]] ||
                fail "Clustering '$1' into '$CLUSTERS' clusters missed some '$field' entries"
        done
    done < <(clusterNums)
}

function pkgTestClusterFields {
    clusterFields "$1" getClusters
}

function pkgTestEndToEndFields {
    clusterFields "$1" getEndToEnd
}

# Test invocation

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

function runTraced {
    # Log stderr in test-data/debug. On failure, send "FAIL" and the debug
    # path to stdout
    read -ra CMD <<<"$@" # Re-parse our args to split packages from functions
    PTH=$(echo "test-data/debug/$*" | sed 's/ /_/g')
    traceTest "${CMD[@]}" 2>> "$PTH"
}

function runTest {
    runTraced "$@" || {
        cat "$PTH" 1>&2
        fail "$* failed"
    }
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
