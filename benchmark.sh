#!/usr/bin/env bash

# Benchmark ML4HS compared to GHC and QuickSpec

BASE=$(dirname "$(readlink -f "$0")")

# Ensure our Nix packages are in use
if echo "$NIX_PATH" | grep "$BASE/nix-support" > /dev/null
then
    true
else
    NIX_PATH=$("$BASE/nix-support/nixPath.sh")
    export NIX_PATH
fi

CACHE=$("$BASE/cacheDir.sh")

[[ -n "$REPETITIONS" ]] || REPETITIONS=2

echo "Benchmarking '$REPETITIONS' packages" >> /dev/stderr

COUNT=0
while [[ "$COUNT" -lt "$REPETITIONS" ]] && read -r LINE
do
    PKG=$(echo "$LINE" | cut -f 1)
    VERSION=$(echo "$LINE" | cut -f 2)
    echo "Benchmarking '$PKG'" >> /dev/stderr
    if ! DIR=$("$BASE/fetchIfNeeded.sh" "$PKG")
    then
        echo "$PKG" >> "$CACHE/unfetchable"
    elif ! "$BASE/benchmarks/benchmark-ghc.sh" "$DIR"
    then
        echo "$DIR" >> "$CACHE/unbuildable"
    elif ! "$BASE/benchmarks/benchmark-features.sh" "$DIR"
    then
        echo "$DIR" >> "$CACHE/featureless"
    else
        # Make sure we run all clusters for this package
        CLUSTERS_TODO=$(clusterCount)
        while read -r CLUSTERS
        do
            "$BASE/benchmarks/benchmark-cluster.sh"  "$DIR" "$CLUSTERS" &&
            "$BASE/benchmarks/benchmark-explore.sh"  "$DIR" "$CLUSTERS" &&
            "$BASE/benchmarks/benchmark-simplify.sh" "$DIR" "$CLUSTERS" &&
            CLUSTERS_TODO=$(( CLUSTERS_TODO - 1 ))
        done < <("$BASE/clusterNums.sh")
        [[ "$CLUSTERS_TODO" -eq 0 ]] &&
            COUNT=$(( COUNT + 1 ))   &&
            markFinished "$DIR"
    fi
done < <("$BASE/shufflePackages.sh")
