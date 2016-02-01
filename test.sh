#!/usr/bin/env bash

# Assertion functions

function fail {
    # Unconditional failure
    [[ "$#" -eq 0 ]] || echo "FAIL $*"
    CODE=1
    return 1
}

function assertNotEmpty {
    # Fails if stdin is empty
    COUNT=$(count "^")
    [[ "$COUNT" -gt 0 ]] || fail "$1"
}

function assertJsonNotEmpty {
    # Takes a JSON array on stdin, fails if it's empty
    COUNT=$(jq -r "length")
    [[ "$COUNT" -gt 0 ]] || fail "$1"
}

function count {
    # Count occurrences of $1 in stdin
    PAT="^"
    [ -n "$1" ] && PAT="$1"
    set +e
    grep -c "$PAT"
    set -e
}

# Data generators

function getRawData {
    F="test-data/$1.rawdata"
    [[ ! -e "$F" ]] &&
        getRawAsts "$1" | runTypes "$1" > "$F"
    cat "$F"
}

function getTypeCmd {
    F="test-data/$1.typeCmd"
    [[ ! -e "$F" ]] &&
        getRawData "$1" | jq -r '.cmd' > "$F"
    cat "$F"
}

function getScopeCmd {
    F="test-data/$1.scopeCmd"
    [[ ! -e "$F" ]] &&
        getRawData "$1" | jq -r '.scopecmd' > "$F"
    cat "$F"
}

function getTypeResults {
    F="test-data/$1.typeResults"
    [[ ! -e "$F" ]] &&
        getRawData "$1" | jq -r '.result' > "$F"
    cat "$F"
}

function getScopeResult {
    F="test-data/$1.scopeResult"
    [[ ! -e "$F" ]] &&
        getRawData "$1" | jq -r '.scoperesult' > "$F"
    cat "$F"
}

function getArities {
    F="test-data/$1.arities"
    [[ ! -e "$F" ]] &&
        getTypeResults "$1" | getArities > "$F"
    cat "$F"
}

function getTypes {
    F="test-data/$1.types"
    [[ ! -e "$F" ]] &&
        getScopeResult "$1" | getTypes > "$F"
    cat "$F"
}

function getArityTagged {
    F="test-data/$1.aritytagged"
    [[ ! -e "$F" ]] &&
        getRawAsts "$1" | tagAsts <(getArities "$1") > "$F"
    cat "$F"
}

function getTypeTagged {
    F="test-data/$1.typetagged"
    [[ ! -e "$F" ]] &&
        getRawAsts "$1" | tagAsts <(getTypes "$1") > "$F"
    cat "$F"
}

function getAsts {
    F="test-data/$1.asts"
    [[ ! -e "$F" ]] &&
        getRawData "$1" | annotateAsts > "$F"
    cat "$F"
}

function getDeps {
    F="test-data/$1.deps"
    [[ ! -e "$F" ]] &&
        getAsts "$1" | getDeps > "$F"
    cat "$F"
}

# Tests

function pkgTestGetRawData {
    getRawData     "$1" | assertJsonNotEmpty "Couldn't get raw data from '$1'"
}

function pkgTestGetTypeCmd {
    getTypeCmd     "$1" | assertNotEmpty "Couldn't get type command from '$1'"
}

function pkgTestGetScopeCmd {
    getScopeCmd    "$1" | assertNotEmpty "Couldn't get scoped command from '$1'"
}

function pkgTestGetTypeResults {
    getTypeResults "$1" | assertNotEmpty "Couldn't get type info from '$1'"
}

function pkgTestGetScopeResult {
    getScopeResult "$1" | assertNotEmpty "Couldn't get scoped type info from '$1'"
}

function pkgTestGetArities {
    getArities     "$1" | assertJsonNotEmpty "Couldn't get arities from '$1'"
}

function pkgTestGetTypes {
    getTypes       "$1" | assertJsonNotEmpty "Couldn't get types from '$1'"
}

function pkgTestGetArityTagged {
    getArityTagged "$1" | assertJsonNotEmpty "Couldn't get ASTs with aritiesfrom '$1'"
}

function pkgTestGetTypeTagged {
    getTypeTagged  "$1" | assertJsonNotEmpty "Couldn't get typed ASTs from '$1'"
}

function pkgTestGetAsts {
    getAsts        "$1" | assertJsonNotEmpty "Couldn't get ASTs from '$1'"
}

function pkgTestAstFields {
    COUNT=$(getAsts "$1" | jq -c 'length')
    PKGS=$(getAsts "$1" | jq -c 'map(.package)  | length')
    MODS=$(getAsts "$1" | jq -c 'map(.module)   | length')
    NAMES=$(getAsts "$1" | jq -c 'map(.name)     | length')
    ASTS=$(getAsts "$1" | jq -c 'map(.ast)      | length')
    TYPES=$(getAsts "$1" | jq -c 'map(.type)     | length')
    ARITIES=$(getAsts "$1" | jq -c 'map(.arity)    | length')
    FEATURES=$(getAsts "$1" | jq -c 'map(.features) | length')
    [[ $COUNT -eq $PKGS     ]] || fail "$FUNCNAME '$1' pkgs"
    [[ $COUNT -eq $MODS     ]] || fail "$FUNCNAME '$1' mods"
    [[ $COUNT -eq $NAMES    ]] || fail "$FUNCNAME '$1' names"
    [[ $COUNT -eq $ASTS     ]] || fail "$FUNCNAME '$1' asts"
    [[ $COUNT -eq $TYPES    ]] || fail "$FUNCNAME '$1' types"
    [[ $COUNT -eq $ARITIES  ]] || fail "$FUNCNAME '$1' arities"
    [[ $COUNT -eq $FEATURES ]] || fail "$FUNCNAME '$1' features"
}

function pkgTestAstLabelled {
    getAsts "$1" | jq -c '.[] | .package' |
        while read -r LINE
        do
            [[ "x$LINE" = "x\"$1\"" ]] || fail "$FUNCNAME $1 $LINE"
        done
}

function pkgTestAllTypeCmdPresent {
    getAsts "$1" | jq -c -r '.[] | .module + "." + .name' |
        while read -r LINE
        do
            getTypeCmd "$1" | grep "('$LINE)" > /dev/null ||
                fail "$LINE not in '$1' type command"
        done
}

function pkgTestNoCoreNames {
    COUNT=$(getAsts "$1" | jq -r '.[] | .name' | count '\.\$')
    [[ "$COUNT" -eq 0 ]] ||
        fail "ASTs for '$1' contain Core names beginning with \$"
}

function pkgTestDeps {
    HAVE=$(getDeps "$1" | jq 'map(has("dependencies")) | all')
    [[ "x$HAVE" = "xtrue" ]] ||
        fail "ASTs for '$1' didn't get dependencies"
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
