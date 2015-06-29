#!/bin/sh

for PACKAGE in directory
do
    OUT=$(./dump-hackage.sh "$PACKAGE")
    COUNT=$(echo "$OUT" | grep -c ^)
    if [[ "$OUT" -eq 0 ]]
    then
        echo "Couldn't get ASTs from '$PACKAGE'"
        exit 1
    fi
    LABELLED=$(echo "$OUT" | grep -c "^$PACKAGE:")
    if [[ "$LABELLED" -eq 0 ]]
    then
        echo "ASTs aren't labelled with '$PACKAGE'"
        exit 1
    fi
done
