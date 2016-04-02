#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq getDeps

set -o pipefail

BASE=$(dirname "$0")

# Using "exit" will only stop the current sub-shell. To stop the whole script,
# we use "trap" to watch for a particular exit code (arbitrarily chosen as 77)
# and propagate it up to kill the whole script.
# See http://unix.stackexchange.com/a/48550/63735

set -E
trap '[ "$?" -ne 77 ] || exit 77' ERR

# Assertion functions

function msg {
    echo -e "$1" 1>&2
}

function fail {
    # Unconditional failure
    msg "FAIL: $*"
    exit 77
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
    PROP=$(echo "$INPUT" | jq -c "map(select(has(\"$1\"))) | length")
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
#EOF
}

# Data generators

function nixed {
    # 'nixed foo bar baz' will call 'foo' from defs-default.nix with arguments
    # '"bar"' and '"baz"'
    NIXED_FUNCTION="$1"
    shift

    NIXED_ARGS=$(printf '"%s" ' "$@")
    NIXED_EXPR="(import ./defs-default.nix).$NIXED_FUNCTION $NIXED_ARGS"

    # Yo dawg, I heard you like tests, so we put a call to this test suite in
    # the annotatedb installer, and calls to the annotatedb installer in this
    # test suite, so you can test while you test.
    # Since infinite recursion can take a while, we limit ourselves to one
    # invocation using NIX_DO_CHECK=0
    NIX_DO_CHECK=0 nix-build --no-out-link -E "$NIXED_EXPR" ||
        fail "Error building '$NIXED_EXPR'"
}

function output {
    cat "$1" || fail "Couldn't dump contents of '$1'"
}

function getRawAstsFile {
    RAWASTSFILE_DUMP=$(nixed downloadAndDump "$1")
    echo "$RAWASTSFILE_DUMP/dump.json"
}

function getRawDataFile {
    RAWDATAFILE_ASTS=$(getRawAstsFile "$1")
    RAWDATAFILE_TYPES=$(nixed runTypes "$RAWDATAFILE_ASTS" "$1")
    echo "$RAWDATAFILE_TYPES/typed.json"
}

function getFinalFile {
    FINALFILE_ASTS=$(getRawAstsFile "$1") || fail
    FINALFILE_ANNOTATED=$(nixed annotate "$FINALFILE_ASTS" "$1") || fail
    echo "$FINALFILE_ANNOTATED/annotated.json"
}

function getRawAsts {
    RAWASTS_FILE=$(getRawAstsFile "$1") || fail
    output "$RAWASTS_FILE"
}

function getRawData {
    RAWDATA_FILE=$(getRawDataFile "$1") || fail
    output "$RAWDATA_FILE"
}

function getFinal {
    FINAL_FILE=$(getFinalFile "$1") || fail
    output "$FINAL_FILE"
}

function getTypeResults {
    getRawData "$1" | jq -r '.result'
}

function getScopeResult {
    getRawData "$1" | jq -r '.scoperesult'
}

function getArities {
    [[ -e "$BASE/getArities" ]] || fail "Couldn't find getArities in '$BASE'"
    getTypeResults "$1" | "$BASE/getArities"
}

function getTypes {
    [[ -e "$BASE/getTypes" ]] || fail "Couldn't find getTypes in '$BASE'"
    getScopeResult "$1" | "$BASE/getTypes"
}

function getArityTagged {
    [[ -e "$BASE/tagAsts" ]] || fail "Couldn't find tagAsts in '$BASE'"
    getRawAsts "$1" | "$BASE/tagAsts" <(getArities "$1") "{}"
}

function getTypeTagged {
    [[ -e "$BASE/tagAsts" ]] || fail "Couldn't find tagAsts in '$BASE'"
    getRawAsts "$1" | "$BASE/tagAsts" <(getTypes "$1") "{}"
}

function getAsts {
    [[ -e "$BASE/annotateAsts" ]] || fail "Couldn't find annotateAsts in '$BASE'"
    getRawData "$1" | "$BASE/annotateAsts"
}

function getDeps {
    [[ -e "$BASE/getDeps" ]] || fail "Couldn't find getDeps in '$BASE'"
    getAsts "$1" | "$BASE/getDeps"
}

# Tests

function pkgTestAllAstsPreserved {
    getRawData "$1" | jq -c '.asts | .[]' |
        while read -r LINE
        do
            NAME=$(echo "$LINE" | jq -r '.name')
             MOD=$(echo "$LINE" | jq -r '.module')
             PKG=$(echo "$LINE" | jq -r '.package')
            PRED=".name == \"$NAME\" and .module == \"$MOD\" and .package == \"$PKG\""
            COUNT=$(getAsts "$1" | jq "map(select($PRED)) | length")
            [[ "$COUNT" -eq 1 ]] ||
                fail "$PKG:$MOD.$NAME was in raw data but not ASTs"
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

function pkgTestDepPackagesSeparateFromVersions {
    DEPPACKAGES=$(getDeps "$1"                                  |
                  jq -cr '.[] | .dependencies | .[] | .package' | sort -u) || {
        fail "Couldn't get packages of '$1' dependencies"
        return 1
    }
    echo "$DEPPACKAGES" | grep -- "-[0-9][0-9.]*$" > /dev/null &&
        fail "Deps of '$1' have versions in their package ID:\n$DEPPACKAGES"

    return 0
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

function runTest {
    # Log stderr in TESTDIR. On failure, send "FAIL" and the debug path to
    # stdout
    read -ra CMD <<<"$@" # Re-parse our args to split packages from functions
    PTH=$(echo "$TESTDIR/$*" | sed 's/ /_/g')
    msg "Logging to '$PTH'"

    traceTest "${CMD[@]}" 2>> "$PTH" || {
        cat "$PTH" 1>&2
        fail "$*"
    }
}

function runTests {
    # Handle a regex, if we've been given one
    if [[ -z "$1" ]]
    then
        TESTS=$(getTests)
    else
        TESTS=$(getTests | grep "$1")
    fi

    while read -r test
    do
        msg "Running test '$test'"

        # $test is either empty, successful or we're exiting with an error
        [[ -z "$test" ]] || runTest "$test"
        [[ "$?" -eq 0 ]] || fail "FAIL: $test"
    done < <(echo "$TESTS")

    msg "All tests passed"
}

TESTDIR=$(mktemp -d '/tmp/annotatedb-test-XXXXX')
runTests "$1"
