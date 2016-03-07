#!/usr/bin/env bash

# Benchmark ML4HS compared to GHC and QuickSpec

BASE=$(dirname "$(readlink -f "$0")")

[[ -n "$REPETITIONS" ]] || REPETITIONS=2

echo "Benchmarking '$REPETITIONS' packages" >> /dev/stderr

COUNT=0
while [[ "$COUNT" -lt "$REPETITIONS" ]] && read -r PKG
do
    echo "Benchmarking '$PKG'" >> /dev/stderr
    if ! DIR=$("$BASE/fetchIfNeeded.sh" "$PKG")
    then
        markUnfetchable "$PKG"
    elif ! "$BASE/benchmarks/benchmark-ghc.sh" "$PKG" "$DIR"
    then
        markUnbenchable "$PKG"
    elif ! "$BASE/benchmarks/benchmark-features.sh" "$PKG" "$DIR"
    then
        markFeatureless "$PKG"
    else
        # Make sure we run all clusters for this package
        CLUSTERS_TODO=$(clusterCount)
        while read -r CLUSTERS
        do
            "$BASE/benchmarks/benchmark-cluster.sh"  "$PKG" "$CLUSTERS" &&
            "$BASE/benchmarks/benchmark-explore.sh"  "$PKG" "$CLUSTERS" &&
            "$BASE/benchmarks/benchmark-simplify.sh" "$PKG" "$CLUSTERS" &&
            CLUSTERS_TODO=$(( CLUSTERS_TODO - 1 ))
        done < <("$BASE/clusterNums.sh")
        [[ "$CLUSTERS_TODO" -eq 0 ]] &&
            COUNT=$(( COUNT + 1 ))   &&
            markFinished "$PKG"
    fi
done < <("$BASE/shufflePackages.sh")
