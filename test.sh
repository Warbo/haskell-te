#! /usr/bin/env nix-shell
#! nix-shell -i bash -p bash jq

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

function allObjectsHave {
    INPUT=$(cat)
    COUNT=$(echo "$INPUT" | jq -c 'length')
    PROP=$(echo "$INPUT" | jq -c "map(.$1) | length")
    [[ "$COUNT" -eq "$PROP" ]]
}

# Find tests by querying the environment for test* and pkgTest* functions

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
xmonad
pandoc
git-annex
hakyll
egison
lens
warp
conduit
ghc-mod
shelly
http-conduit
yesod-core
EOF
}

# Data generators; expensive calls should cache in test-data/

function getRawAsts {
    F="test-data/$1.rawasts"
    [[ ! -e "$F" ]] &&
        nix-shell -p cabal2db --run "dump-hackage '$1'" > "$F"
    cat "$F"
}

function getRawData {
    [[ -e "$BASE/runTypes" ]] || fail "Couldn't find runTypes in '$BASE'"
    F="test-data/$1.rawdata"
    [[ ! -e "$F" ]] &&
        getRawAsts "$1" | "$BASE/runTypes" "$1" > "$F"
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
    [[ -e "$BASE/getArities" ]] || fail "Couldn't find getArities in '$BASE'"
    F="test-data/$1.arities"
    [[ ! -e "$F" ]] &&
        getTypeResults "$1" | "$BASE/getArities" > "$F"
    cat "$F"
}

function getTypes {
    [[ -e "$BASE/getTypes" ]] || fail "Couldn't find getTypes in '$BASE'"
    F="test-data/$1.types"
    [[ ! -e "$F" ]] &&
        getScopeResult "$1" | "$BASE/getTypes" > "$F"
    cat "$F"
}

function getArityTagged {
    [[ -e "$BASE/tagAsts" ]] || fail "Couldn't find tagAsts in '$BASE'"
    F="test-data/$1.aritytagged"
    [[ ! -e "$F" ]] &&
        getRawAsts "$1" | "$BASE/tagAsts" <(getArities "$1") > "$F"
    cat "$F"
}

function getTypeTagged {
    [[ -e "$BASE/tagAsts" ]] || fail "Couldn't find tagAsts in '$BASE'"
    F="test-data/$1.typetagged"
    [[ ! -e "$F" ]] &&
        getRawAsts "$1" | "$BASE/tagAsts" <(getTypes "$1") > "$F"
    cat "$F"
}

function getAsts {
    [[ -e "$BASE/annotateAsts" ]] || fail "Couldn't find annotateAsts in '$BASE'"
    F="test-data/$1.asts"
    [[ ! -e "$F" ]] &&
        getRawData "$1" | "$BASE/annotateAsts" > "$F"
    cat "$F"
}

function getDeps {
    [[ -e "$BASE/getDeps" ]] || fail "Couldn't find getDeps in '$BASE'"
    F="test-data/$1.deps"
    [[ ! -e "$F" ]] &&
        getAsts "$1" | "$BASE/getDeps" > "$F"
    cat "$F"
}

function getFinal {
    [[ -e "$BASE/annotateDb" ]] || fail "Couldn't find annotateDb in '$BASE'"
    F="test-data/$1.final"
    [[ ! -e "$F" ]] &&
        getRawAsts "$1" | "$BASE/annotateDb" "$1" > "$F"
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
    for FIELD in package module name ast type arity features
    do
        getAsts "$1" | allObjectsHave "$FIELD" ||
            fail "ASTs for '$1' don't all have '$FIELD'"
    done
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

function pkgTestFinalHasAllTags {
    for FIELD in package module name ast type arity dependencies
    do
        getFinal "$1" | allObjectsHave "$FIELD" ||
            fail "Annotated DB of '$1' is missing some '$FIELD'"
    done
}

function testTagging {
    INPUT1='[{"name": "n1", "module": "M1"}, {"name": "n2", "module": "M2"}]'
    INPUT2='[{"name": "n2", "module": "M2", "foo": "bar"}]'
    RESULT=$(echo "$INPUT1" | "$BASE/tagAsts" <(echo "$INPUT2"))
    TYPE=$(echo "$RESULT" | jq 'type')
    [[ "x$TYPE" == 'x"array"' ]] || fail "tagAsts gave '$TYPE' not array"
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
