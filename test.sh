#! /usr/bin/env nix-shell
#! nix-shell -i bash -p cabal2db annotatedb jq

BASE=$(dirname "$0")

# Assertion functions

function fail {
    # Unconditional failure
    [[ "$#" -eq 0 ]] || echo "FAIL $*"
    CODE=1
    return 1
}

function assertNotEmpty {
    # Fails if stdin is empty
    COUNT=$(grep -c "^")
    [[ "$COUNT" -gt 0 ]] || fail "$1"
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
            echo "Can't get raw ASTs for '$pkg', skipping"    >> /dev/stderr
            echo "Flaky package or bug in Cabal2DB, see $PTH" >> /dev/stderr
            continue
        }
        runTraced getAsts "$pkg" > /dev/null || {
            echo "Can't get ASTs for '$pkg', skipping"          >> /dev/stderr
            echo "Flaky package or bug in annotatedb, see $PTH" >> /dev/stderr
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
xmonad
hakyll
EOF
}

# Data generators

function getRawAsts {
    F="test-data/$1.rawasts"
    [[ ! -e "$F" ]] && {
        # Hide errors, but log them vai set -x debugging
        OUTPUT=$( { dump-hackage "$1" > "$F"; } 2>&1 ) || {
            fail "Couldn't get raw ASTs for '$1'"
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
    [[ ! -e "$F" ]] &&
        getAsts "$1" | "$BASE/extractFeatures" > "$F"
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
    [[ ! -e "$F" ]] &&
        getAsts "$1" | "$BASE/cluster" > "$F"
    cat "$F"
}

# Feature extraction tests

function pkgTestGetFeatures {
    getFeatures "$1" | assertNotEmpty "Couldn't get features from '$1'"
}

function pkgTestFeaturesConform {
    FEATURELENGTHS=$(getFeatures "$1" | jq -r '.[] | .features | length')
    COUNT=$(echo "$FEATURELENGTHS" | head -n 1)
    echo "$FEATURELENGTHS" | while read -r LINE
    do
        if [[ "$LINE" -ne "$COUNT" ]]
        then
            fail "Found '$LINE' features, was expecting '$COUNT'"
        fi
    done
}

# Clustering tests; each is tested with the feature extraction output, and via
# the top-level "cluster" command

function clusterNums {
    # The number of clusters to test with. Since it's expensive, we use the same
    # numbers each time, so the caches can be re-used.
    cat <<EOF
1
2
11
EOF
}

function allClustered {
    while read -r CLUSTERS
    do
        if "$2" "$1" | jq '.[] | .tocluster' | grep "false" > /dev/null
        then
            fail "Clustering '$1' into '$CLUSTERS' clusters didn't include everything"
        fi
    done < <(clusterNums)
}

function pkgTestAllClustered {
    allClustered "$1" getClusters
}

function pkgTestAllEndToEnd {
    allClustered "$1" getEndToEnd
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

function runTraced {
    # Log stderr in test-data/debug. On failure, send "FAIL" and the debug
    # path to stdout
    read -ra CMD <<<"$@" # Re-parse our args to split packages from functions
    PTH=$(echo "test-data/debug/$*" | sed 's/ /_/g')
    traceTest "${CMD[@]}" 2>> "$PTH"
}

function runTest {
    runTraced "$@" || fail "$* failed, see $PTH"
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
