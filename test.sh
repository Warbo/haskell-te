#!/usr/bin/env bash
set -e

# Calls Nix to evaluate tests, but output is messy and it might die silently
function runIgnoreFailure {
    nix-instantiate --read-write-mode --show-trace --eval \
                    -E 'import ./nix-support/test.nix'
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

# Run tests, and also move any TAP results in stderr into stdout
function report {
    #
    #     ,--stdout+TAP---------------------------,--> stdout + TAP
    #    /                                       /
    # run                              ,--TAP---'
    #    \                            /
    #     `--stderr+TAP--> stderrToTap
    #                                 \
    #                                  `--stderr-----> stderr (no TAP)
    #
    { run 2>&1 1>&3 | stderrToTap; } 3>&1
    return "${PIPESTATUS[0]}"
}

# Sends TAP results to stdout, everything else to stderr
function stderrToTap {
    while read -r ERRLINE
    do
        if echo "$ERRLINE" | grep "^trace: \(not \)\?ok" > /dev/null
        then
            echo "$ERRLINE" | sed -e 's/^trace: //g'
        else
            echo "$ERRLINE" 1>&2
        fi
    done
}

# Numbers are optional, but some tools like faucet complain without them
function numberedReport {
    COUNT=0
    while read -r LINE
    do
        if echo "$LINE" | grep "^\(not \)\?ok" > /dev/null
        then
            COUNT=$(( COUNT + 1 ))
            echo "$LINE" | sed -e "s/ok [0-9]*/ok $COUNT /"
        else
            echo "$LINE"
        fi
    done < <(report)
    echo "1..$COUNT"
}

numberedReport
