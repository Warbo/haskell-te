#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq haskellPackages.ShellCheck cabal2db annotatedb recurrent-clustering mlspec
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

function clusterNums {
    # Re-use the same numbers of clusters across tests, so we can use cached
    # results
    cat <<EOF
1
2
11
EOF
}

function getTestPkgs {
    # A list of packages to test with
    cat <<EOF
list-extras
xmonad
hakyll
EOF
}

function getRawAsts {
    F="test-data/$1.rawasts"
    [[ -e "$F" ]] || {
        dump-hackage "$1" > "$F" || {
            fail "Error getting ASTs for '$1'"
            return 1
        }
    }
    cat "$F"
}

function getAsts {
    F="test-data/$1.asts"
    [[ -e "$F" ]] || {
        getRawAsts "$1" | annotateDb "$1" > "$F" || {
            fail "Error annotating ASTs for '$1'"
            return 1
        }
    }
    cat "$F"
}

function getClusters {
    [[ -n "$CLUSTERS" ]] || {
        fail "No CLUSTERS for getClusters"
        return 1
    }
    export CLUSTERS
    F="test-data/$1.clusters.$CLUSTERS"
    [[ -e "$F" ]] || {
        getAsts "$1" | cluster > "$F" || {
            fail "Error clustering '$1' into '$CLUSTERS' clusters"
            return 1
        }
    }
    cat "$F"
}

function getFormattedClusters {
    [[ -n "$CLUSTERS" ]] || {
        fail "No CLUSTERS for getFormattedClusters"
        return 1
    }
    export CLUSTERS
    F="test-data/$1.formatted.$CLUSTERS"
    [[ -e "$F" ]] || {
        getClusters "$1" | "$BASE/format-exploration.sh" > "$F" || {
            fail "Error formatting '$CLUSTERS' clusters for '$1'"
            return 1
        }
    }
    cat "$F"
}

function getEquations {
    [[ -n "$CLUSTERS" ]] || {
        fail "No CLUSTERS for getEquations"
        return 1
    }
    export CLUSTERS
    F="test-data/$1.rawEquations.$CLUSTERS"
    [[ -e "$F" ]] || {
        getFormattedClusters "$1" | "$BASE/run-exploration.sh" > "$F" || {
            fail "Error running run-exploration.sh for '$1' with '$CLUSTERS' clusters"
            return 1
        }
    }
    cat "$F"
}

function getEndToEnd {
    [[ -n "$CLUSTERS" ]] || {
        fail "No CLUSTERS for getEquations"
        return 1
    }
    export CLUSTERS
    export ML4HSDIR="$PWD/test-data"
    F="test-data/$1.endToEnd.$CLUSTERS"
    [[ -e "$F" ]] || {
        "$BASE/ml4hs.sh" "$1" > "$F" || {
            fail "Error running ml4hs.sh on '$1' with '$CLUSTERS' clusters"
            return 1
        }
    }
    cat "$F"
}

# Tests requiring a package as argument.

function pkgTestValidFormatting {
    while read -r CLUSTERS
    do
        FORMATTED=$(getFormattedClusters "$1") || {
            fail "Couldn't get '$CLUSTERS' formatted clusters for '$1'"
            return 1
        }
        LENGTH=$(echo "$FORMATTED" | jq -c 'length') || {
            fail "Can't read '$CLUSTERS' formatted clusters for '$1'"
            continue
        }
        [[ "$LENGTH" -eq "$CLUSTERS" ]] || [[ "$LENGTH" -lt "$CLUSTERS" ]] ||
            fail "Formatted '$LENGTH' clusters for '$1' instead of '$CLUSTERS'"
    done < <(clusterNums)
}

function pkgTestOnlyQuickspecableFormatted {
    while read -r CLUSTERS
    do
        QS=$(getFormattedClusters "$1" | jq 'map(.[] | .quickspecable) | all') || {
            fail "Couldn't see if '$1' with '$CLUSTERS' clusters are quickspecable"
            return 1
        }
        [[ "x$QS" = "xtrue" ]] ||
            fail "Got '$QS' not 'true' for '$1' in '$CLUSTERS' clusters"
    done < <(clusterNums)
}

# We run tests of the equations twice: once on the equations built from the
# cache, and once with the output of ml4hs.sh, to ensure that they're the same

function checkExitCode {
    while read -r CLUSTERS
    do
        "$2" "$1" || fail "'$2' exited with error for '$1'"
    done < <(clusterNums)
}


function pkgTestEquationsCode {
    checkExitCode "$1" getEquations
}

function pkgTestEndToEndCode {
    checkExitCode "$1" getEndToEnd
}

###

function checkJsonEqs {
    while read -r CLUSTERS
    do
        OUTPUT=$("$2" "$1")
        LENGTH=$(echo "$OUTPUT" | grep '^{' | jq -cs 'length')
        [[ "$LENGTH" -gt 0 ]] ||
            fail "'$2' on '$1' produced 0 JSON objects '$OUTPUT'"
    done < <(clusterNums)
}

function pkgTestClusterJson {
    checkJsonEqs "$1" getEquations
}

function pkgTestEndToEndJson {
    checkJsonEqs "$1" getEndToEnd
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
