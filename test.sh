#!/usr/bin/env bash
set -e

# Calls Nix to evaluate tests, but output is messy and it might die silently
function runIgnoreFailure {
    nix-build --show-trace "./nix-support/test.nix"
    #nix-instantiate --read-write-mode --show-trace --eval \
    #                -E 'import ./nix-support/test.nix'
}

# Runs tests, with an additional pass/fail for whether the test command died
function run {
    if runIgnoreFailure
    then
        echo "ok Test suite exited gracefully"
    else
        echo "not ok Test suite exited gracefully"
        return 1
    fi
}

# Numbers are optional, but some tools like faucet complain without them
function numberedReport {
    COUNT=0
    while read -r LINE
    do
        if echo "$LINE" | grep "^\(not \)\?ok -" > /dev/null
        then
            COUNT=$(( COUNT + 1 ))
            echo "$LINE" | sed -e "s/ok [0-9]*/ok $COUNT /"
        else
            echo "$LINE"
        fi
    done < <(run)
    echo "1..$COUNT"
}

numberedReport
