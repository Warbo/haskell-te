#!/usr/bin/env bash

# Get the last lot of stdout for the given benchmark

function upToDashes {
    while read -r LINE
    do
        if [[ "x$LINE" = "x-----" ]]
        then
            break
        else
            echo "$LINE"
        fi
    done
}

EXPECT=$(echo "$BENCHMARK_COMMAND $BENCHMARK_ARGS" | tr -dc '[:alnum:]')
for F in "$BENCH_DIR"/outputs/*.stdout
do
    NAME=$(basename "$F" .stdout)
    FOUND=$(echo "$NAME" | tr -dc '[:alnum:]')
    if [[ "x$FOUND" = "x$EXPECT" ]]
    then
        echo "Found stdout in '$F'" >> /dev/stderr
        # Get everything following last occurrence of -----
        tac "$F" | upToDashes | tac
        exit 0
    fi
done

echo "Didn't find stdout, aborting" >> /dev/stderr
exit 1
