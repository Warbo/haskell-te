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

function testGetFeatures {
    getFeatures "$1" | assertNotEmpty "Couldn't get features from '$1'"
}

function countCommas {
    tr -dc ',' | wc -c
}

function testFeaturesUniform {
    COUNT=$(getFeatures "$1" | head -n 1 | countCommas)
    getFeatures "$1" | while read LINE
                       do
                           THIS=$(printf "$LINE" | countCommas)
                           if [[ "$THIS" -ne "$COUNT" ]]
                           then
                               fail "'$LINE' doesn't have $COUNT commas"
                           fi
                       done
}

function testPackage {
    testGetAst          "$1"
    testAstLabelled     "$1"
    testGetFeatures     "$1"
    testFeaturesUniform "$1"
}

testPackage "directory"

exit "$CODE"
