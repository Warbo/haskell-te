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

while read -r F
do
    echo "INFO: Found stdout in '$F'" >> /dev/stderr
    # Get everything following last occurrence of -----
    tac "$F" | upToDashes | tac
    exit 0
done < <(find "$BENCH_DIR"/outputs -name "*.stdout")

echo "ERROR: Didn't find stdout, aborting" >> /dev/stderr
exit 1
