#! /usr/bin/env nix-shell
#! nix-shell -p jq -p haskellPackages.ShellCheck -i bash
shopt -s nullglob
source common.sh

# Simple test suite for ML4HS:
#  - Given no arguments, all tests will run
#  - Given a regex as argument, only matching tests will be called
#  - Intermediate results are cached in test-data/
#  - There is no cache invalidation, so just delete the directory as needed
#  - Functions with names beginning with "test" will be called automatically
#  - Functions with names beginning with "testPkg" will be called automatically
#    with a selection of package names as their first argument

# Assertion functions

function fail {
    [[ "$#" -eq 0 ]] || echo "FAIL $*"
    CODE=1
    return 1
}

function absent {
    while read LINE
    do
        if [[ "x$LINE" = "x$1" ]]
        then
            return 1
        fi
    done
    return 0
}

function assertNotEmpty {
    COUNT=$(count "^")
    [[ "$COUNT" -gt 0 ]] || fail "$1"
}

function assertJsonNotEmpty {
    COUNT=$(jqLog -r "length")
    [[ "$COUNT" -gt 0 ]] || fail "$1"
}

function count {
    PAT="^"
    [ -n "$1" ] && PAT="$1"
    set +e
    grep -c "$PAT"
    set -e
}

# Functions to get data; these should read/write from/to the test-data/ cache

function getFunctions {
    # Get a list of declared functions
    declare -F | cut -d ' ' -f 3-
}

function getPkgTests {
    # Get a list of tests which require a package
    getFunctions | grep '^pkgTest'
}

function getTests {
    # Get a list of all test functions
    getFunctions | grep '^test'
}

function getTestPkgs {
    cat <<EOF
data-stringmap
MissingH
attoparsec
directory
quickspec
EOF
}

function getRawJson {
    F="test-data/$1.rawjson"
    [[ ! -e "$F" ]] &&
        NOFORMAT="true" ./dump-hackage.sh "$1" > "$F"
    cat "$F"
}

function getRawAsts {
    F="test-data/$1.rawasts"
    [[ ! -e "$F" ]] &&
        ./dump-hackage.sh "$1" > "$F"
    cat "$F"
}

function getRawData {
    F="test-data/$1.rawdata"
    [[ ! -e "$F" ]] &&
        getRawAsts "$1" | ./runTypes.sh "$1" > "$F"
    cat "$F"
}

function getTypeCmd {
    F="test-data/$1.typeCmd"
    [[ ! -e "$F" ]] &&
        getRawData "$1" | jqLog -r '.cmd' > "$F"
    cat "$F"
}

function getTypeResults {
    F="test-data/$1.typeResults"
    [[ ! -e "$F" ]] &&
        getRawData "$1" | jqLog -r '.result' > "$F"
    cat "$F"
}

function getScopeCmd {
    F="test-data/$1.scopeCmd"
    [[ ! -e "$F" ]] &&
        getRawData "$1" | jqLog -r '.scopecmd' > "$F"
    cat "$F"
}

function getScopeResult {
    F="test-data/$1.scopeResult"
    [[ ! -e "$F" ]] &&
        getRawData "$1" | jqLog -r '.scoperesult' > "$F"
    cat "$F"
}

function getTypes {
    F="test-data/$1.types"
    [[ ! -e "$F" ]] &&
        getScopeResult "$1" | ./getTypes.sh > "$F"
    cat "$F"
}

function getArities {
    F="test-data/$1.arities"
    [[ ! -e "$F" ]] &&
        getTypeResults "$1" | ./getArities.sh > "$F"
    cat "$F"
}

function getTypeTagged {
    F="test-data/$1.typetagged"
    [[ ! -e "$F" ]] &&
        getRawAsts "$1" | ./tagAsts.sh <(getTypes "$1") > "$F"
    cat "$F"
}

function getArityTagged {
    F="test-data/$1.aritytagged"
    [[ ! -e "$F" ]] &&
        getRawAsts "$1" | ./tagAsts.sh <(getArities "$1") > "$F"
    cat "$F"
}

function getFeatures {
    F="test-data/$1.features"
    [[ ! -e "$F" ]] &&
        getRawAsts "$1" | ./extractFeatures.sh > "$F"
    cat "$F"
}

function getAsts {
    F="test-data/$1.asts"
    [[ ! -e "$F" ]] &&
        getRawData "$1" | ./annotateAsts.sh > "$F"
    cat "$F"
}

function getClusters {
    F="test-data/$1.clusters"
    [[ ! -e "$F" ]] &&
        getAsts "$1" | ./cluster.sh > "$F"
    cat "$F"
}

function getProjects {
    mkdir -p test-data/projects
    F="test-data/$1.projects"
    if [[ ! -e "$F" || ! -e "test-data/projects/$1" ]]
    then
        rm     "$F"                    2> /dev/null || true
        rm -rf "test-data/projects/$1" 2> /dev/null || true
        mkdir -p "test-data/projects/$1"
        getClusters "$1" | ./make-projects.sh "test-data/projects/$1" > "$F"
    fi
    cat "$F"
}

function getNixedProjects {
    getProjects "$1" || return 1
    mkdir -p test-data/nixed
    if [[ ! -e "test-data/nixed/$1" ]]
    then
        cp -r "test-data/projects/$1" "test-data/nixed/$1"

        ./nix-projects.sh < <(for PROJECT in "test-data/nixed/$1"/*
                              do
                                  readlink -f "$PROJECT"
                              done) || return 1
    fi
}

# Tests requiring a package as argument

function pkgTestGetRawJson {
    getRawJson     "$1" | assertNotEmpty "Couldn't get raw JSON from '$1'"
}

function pkgTestGetRawAsts {
    getRawAsts     "$1" | assertJsonNotEmpty "Couldn't get raw ASTs from '$1'"
}

function pkgTestGetRawData {
    getRawData     "$1" | assertJsonNotEmpty "Couldn't get raw data from '$1'"
}

function pkgTestGetTypeCmd {
    getTypeCmd     "$1" | assertNotEmpty "Couldn't get type command from '$1'"
}

function pkgTestGetTypeResults {
    getTypeResults "$1" | assertNotEmpty "Couldn't get type info from '$1'"
}

function pkgTestGetScopeCmd {
    getScopeCmd    "$1" | assertNotEmpty "Couldn't get scoped command from '$1'"
}

function pkgTestGetScopeResult {
    getScopeResult "$1" | assertNotEmpty "Couldn't get scoped type info from '$1'"
}

function pkgTestGetTypes {
    getTypes       "$1" | assertJsonNotEmpty "Couldn't get types from '$1'"
}

function pkgTestGetArities {
    getArities     "$1" | assertJsonNotEmpty "Couldn't get arities from '$1'"
}

function pkgTestGetTypeTagged {
    getTypeTagged  "$1" | assertJsonNotEmpty "Couldn't get typed ASTs from '$1'"
}

function pkgTestGetArityTagged {
    getArityTagged "$1" | assertJsonNotEmpty "Couldn't get ASTs with aritiesfrom '$1'"
}

function pkgTestGetAsts {
    getAsts        "$1" | assertJsonNotEmpty "Couldn't get ASTs from '$1'"
}

function pkgTestAstFields {
       COUNT=$(getAsts "$1" | jqLog -c 'length')
        PKGS=$(getAsts "$1" | jqLog -c 'map(.package)  | length')
        MODS=$(getAsts "$1" | jqLog -c 'map(.module)   | length')
       NAMES=$(getAsts "$1" | jqLog -c 'map(.name)     | length')
        ASTS=$(getAsts "$1" | jqLog -c 'map(.ast)      | length')
       TYPES=$(getAsts "$1" | jqLog -c 'map(.type)     | length')
     ARITIES=$(getAsts "$1" | jqLog -c 'map(.arity)    | length')
    FEATURES=$(getAsts "$1" | jqLog -c 'map(.features) | length')
    [[ $COUNT -eq $PKGS     ]] || fail "$FUNCNAME '$1' pkgs"
    [[ $COUNT -eq $MODS     ]] || fail "$FUNCNAME '$1' mods"
    [[ $COUNT -eq $NAMES    ]] || fail "$FUNCNAME '$1' names"
    [[ $COUNT -eq $ASTS     ]] || fail "$FUNCNAME '$1' asts"
    [[ $COUNT -eq $TYPES    ]] || fail "$FUNCNAME '$1' types"
    [[ $COUNT -eq $ARITIES  ]] || fail "$FUNCNAME '$1' arities"
    [[ $COUNT -eq $FEATURES ]] || fail "$FUNCNAME '$1' features"
}

function pkgTestAstLabelled {
    getAsts "$1" | jqLog -c '.[] | .package' |
        while read -r LINE
        do
            [[ "x$LINE" = "x\"$1\"" ]] || fail "$FUNCNAME $1 $LINE"
        done
}

function pkgTestAllTypeCmdPresent {
    getAsts "$1" | jqLog -c -r '.[] | .module + "." + .name' |
        while read -r LINE
        do
            getTypeCmd "$1" | grep "('$LINE)" > /dev/null ||
                fail "$LINE not in '$1' type command"
        done
}

function pkgTestNoCoreNames {
    COUNT=$(getAsts "$1" | jqLog -r '.[] | .name' | count '\.\$')
    [[ "$COUNT" -eq 0 ]] ||
        fail "ASTs for '$1' contain Core names beginning with \$"
}

function pkgTestGetFeatures {
    getFeatures "$1" | assertNotEmpty "Couldn't get features from '$1'"
}

function countCommas {
    tr -dc ',' | wc -c
}

function pkgTestFeaturesUniform {
    RAWFEATURES=$(getFeatures "$1" | jqLog -r '.[] | .features' | grep ",")
    COUNT=$(echo "$RAWFEATURES" | head -n 1 | countCommas)
    echo "$RAWFEATURES" |
        while read LINE
        do
            THIS=$(echo "$LINE" | countCommas)
            if [[ "$THIS" -ne "$COUNT" ]]
            then
                fail "'$LINE' doesn't have $COUNT commas"
            fi
        done
}

function pkgTestHaveAllClusters {
    # FIXME: Make cluster number configurable (eg. so we can have it vary based
    # on the number of definitions)
    COUNT=$(getClusters "$1" | jqLog -r 'length')
    if [[ "$COUNT" -ne 4 ]]
    then
        fail "Found $COUNT clusters for '$1' instead of 4"
    fi
}

function pkgTestClusterFields {
    COUNT=$(getClusters "$1" | jqLog -r '.[] | length')
    getClusters "$1" | jqLog 'map(select(has("")))'
}

function pkgTestProjectsMade {
    getProjects "$1" |
        while read PROJECT
        do
            if [[ ! -e "$PROJECT" ]]
            then
                fail "Directory '$PROJECT' not made for '$1'"
            fi
        done
}

function pkgTestNixFilesMade {
    NIXED=$(getNixedProjects "$1") || return 1
    while read PROJECT
    do
        if [[ ! -e "$PROJECT" ]]
        then
            fail "'$PROJECT' not found for '$1'"
        fi
        if [[ ! -e "$PROJECT/shell.nix" ]]
        then
            fail "'$PROJECT/shell.nix' missing for '$1'"
        fi
    done < <(echo "$NIXED")
}

function pkgTestNixProjectsRun {
    getNixedProjects "$1" | ./run-projects.sh
}

# Test functions

function testPackages {
    # Run all package tests on all test packages
    PKGERR=0
    while read pkg
    do
        while read test
        do
            runTest "$test" "$pkg" || PKGERR=1
        done < <(getPkgTests)
    done < <(getTestPkgs)
    return "$PKGERR"
}

function testTagging {
    INPUT1='[{"name": "n1", "module": "M1"}, {"name": "n2", "module": "M2"}]'
    INPUT2='[{"name": "n2", "module": "M2", "foo": "bar"}]'
    RESULT=$(echo "$INPUT1" | ./tagAsts.sh <(echo "$INPUT2"))
    TYPE=$(echo "$RESULT" | jqLog 'type')
    [[ "x$TYPE" == 'x"array"' ]] || fail "tagAsts.sh gave '$TYPE' not array"
}

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

function testJqLogLogs {
    COUNT=0
    while read line
    do
        COUNT=$((COUNT + 1))
        echo "$line" | grep "^\[jqLog fibble]: " > /dev/null
    done < <(jqLog fibble 2>&1)
    [[ "$COUNT" -gt 0 ]] || fail "Errors got lost"
}

function testJqLogWorks {
    X=$(echo '{"foo": 10, "bar": 20}' | jqLog '.foo')
    [[ "$X" -eq 10 ]] || fail "jqLog expressions fail ($X)"

    X=$(echo -e '{"foo": 10}\n{"foo": 11}' | jqLog -c -s 'map(.foo)')
    [[ "$X" = "[10,11]" ]] || fail "jqLog arguments fail ($X)"
}

function testNoNakedJq {
    # We should be using jqLog rather than jq
    NAKERR=0
    for file in *.sh
    do
        if [[ ! "$file" = "common.sh" ]]
        then
            NAKED=$(grep "^[^#]*jq[^L]" < "$file")
            if [[ -n "$NAKED" ]]
            then
                fail "Please use jqLog in $file ($NAKED)"
                NAKERR=1
            fi
        fi
    done
    return "$NAKERR"
}

# Test invocation

function runTest {
    { "$@" && echo "PASS $*"; } || { echo "FAIL $*"; return 1; }
}

function runTests {
    CODE=0
    if [[ -z "$1" ]]
    then
        TESTS=$(getTests)
    else
        TESTS=$(getTests | grep "$1")
    fi
    while read test
    do
        [[ -z "$test" ]] || runTest "$test" || CODE=1
    done < <(echo "$TESTS")
    return "$CODE"
}

# We cache intermediate results in test-data. We have no cache invalidation,
# just delete it whenever you like.
mkdir -p test-data

runTests "$1"
