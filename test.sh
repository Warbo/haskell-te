#!/bin/sh

# Exit code. Can stay at 0 or increase to 1. Should NEVER decrease from 1.
CODE=0

# We cache intermediate results in test-data. We have no cache invalidation,
# just delete it whenever you like.
mkdir -p test-data

function fail {
    CODE=1
    echo "FAIL: $1"
}

function getAst {
    if [[ ! -e "test-data/$1.ast" ]]
    then
        # We use dump-hackage rather than dump-package directly, since it works
        # in a temporary directory
        ./dump-hackage.sh "$1" > "test-data/$1.ast"
    fi
    cat "test-data/$1.ast"
}

function getFeatures {
    if [[ ! -e "test-data/$1.features" ]]
    then
        getAst "$1" | ./extractFeatures.sh > "test-data/$1.features"
    fi
    cat "test-data/$1.features"
}

function getClusterData {
    if [[ ! -e "test-data/$1.clusterdata" ]]
    then
        getFeatures "$1" | ./cluster.sh > "test-data/$1.clusterdata"
    fi
    cat "test-data/$1.clusterdata"
}

function getClusters {
    if [[ ! -e "test-data/$1.clusters" ]]
    then
        getClusterData "$1" | ./lineUp.sh > "test-data/$1.clusters"
    fi
    cat "test-data/$1.clusters"
}

function getProjects {
    if [[ ! -e "test-data/$1.projects" ]]
    then
        mkdir -p "test-data/projects"
        getClusters "$1" | ./make-projects.sh "test-data/projects" > "test-data/$1.projects"
    fi
    cat "test-data/$1.projects"
}

function getNixedProjects {
    if [[ ! -e "test-data/$1.nixed" ]]
    then
        if [[ -e "test-data/nixed" ]]
        then
            rm -rf "test-data/nixed"
        fi
        cp -r "test-data/projects" "test-data/nixed"
        (shopt -s nullglob;
         for PROJECT in test-data/nixed/*
         do
             readlink -f "$PROJECT" >> "test-data/$1.nixed"
         done)
        ./nix-projects.sh < "test-data/$1.nixed"
    fi
    cat "test-data/$1.nixed"
}

function assertNotEmpty {
    COUNT=$(grep -c ^)
    if [[ "$COUNT" -eq 0 ]]
    then
        fail "$1"
    fi
}

function testGetAst {
    getAst "$1" | assertNotEmpty "Couldn't get ASTs from '$1'"
}

function testAstLabelled {
    COUNT=$(getAst "$1" | grep -c "^$1:")
    if [[ "$COUNT" -eq 0 ]]
    then
        fail "ASTs aren't labelled with '$1'"
    fi
}

function testNoCoreNames {
    COUNT=$(getAst "$1" | grep -c '\.\$')
    if [[ "$COUNT" -ne 0 ]]
    then
        fail "ASTs for '$1' contain Core names beginning with \$"
    fi
}

function testGetFeatures {
    getFeatures "$1" | assertNotEmpty "Couldn't get features from '$1'"
}

function countCommas {
    tr -dc ',' | wc -c
}

function testFeaturesUniform {
    COUNT=$(getFeatures "$1" | cut -d '"' -f 3- | head -n 1 | countCommas)
    getFeatures "$1" | while read LINE
                       do
                           THIS=$(printf "$LINE" | cut -d '"' -f 3- |
                                         countCommas)
                           if [[ "$THIS" -ne "$COUNT" ]]
                           then
                               fail "'$LINE' doesn't have $COUNT commas"
                           fi
                       done
}

function testHaveAllClusters {
    # FIXME: Make cluster number configurable (eg. so we can have it vary based
    # on the number of definitions)
    COUNT=$(getClusterData "$1" | cut -f 1 | sort -u | wc -l)
    if [[ "$COUNT" -ne 4 ]]
    then
        fail "Found $COUNT clusters for '$1' instead of 4"
    fi
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

function testClusterAllNames {
    INNAMES=$(getAst "$1" | cut -d '"' -f 1-2 | while read BIT
                                                do
                                                    echo "${BIT}\""
                                                done)
    OUTNAMES=$(getClusterData "$1" | cut -f 2)
    echo "$INNAMES"  | while read NAME
                       do
                           if echo "$OUTNAMES" | absent "$NAME"
                           then
                               fail "'$NAME' occurs in '$1' ASTs but not features"
                           fi
                       done
    echo "$OUTNAMES" | while read NAME
                       do
                           if echo "$INNAMES"  | absent "$NAME"
                           then
                               fail "'$NAME' occurs in '$1' features but not ASTs"
                           fi
                       done
}

function testGetClusterCount {
    # NOTE: `wc -l` counts \n characters, so we subtract 1
    # FIXME: Make 4 configurable via and environment variable
    COUNT=$(getClusters "$1" | wc -l)
    if [[ "$COUNT" -ne 3 ]]
    then
        fail "Not enough clusters for '$1' (got $COUNT expected 4)"
    fi
}

function testProjectsMade {
    getProjects "$1" |
        while read PROJECT
        do
            if [[ ! -e "$PROJECT" ]]
            then
                fail "Directory '$PROJECT' not made for '$1'"
            fi
        done
}

function testNixFilesMade {
    getNixedProjects "$1" | while read PROJECT
                            do
                                if [[ ! -e "$PROJECT" ]]
                                then
                                    fail "'$PROJECT' not found for '$1'"
                                fi
                                if [[ ! -e "$PROJECT/shell.nix" ]]
                                then
                                    fail "'$PROJECT/shell.nix' missing for '$1'"
                                fi
                            done
}

function testNixProjectsRun {
    getNixedProjects "$1" | ./run-projects.sh
}

function testPackage {
    testGetAst          "$1"
    testAstLabelled     "$1"
    testNoCoreNames     "$1"
    testGetFeatures     "$1"
    testFeaturesUniform "$1"
    testHaveAllClusters "$1"
    testClusterAllNames "$1"
    testGetClusterCount "$1"
    testProjectsMade    "$1"
    testNixFilesMade    "$1"
    testNixProjectsRun  "$1"
}

testPackage "directory"

exit "$CODE"
