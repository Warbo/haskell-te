#!/usr/bin/env bash

# Benchmark ML4HS compared to GHC and QuickSpec

function info {
    echo -e "INFO: $1" >> /dev/stderr
}

function warn {
    echo -e "WARNING: $1" >> /dev/stderr
    return 1
}

function abort {
    echo -e "ERROR: $1" >> /dev/stderr
    exit 1
}

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")

# Ensure our Nix packages are in use
echo "$NIX_PATH" | grep "$BASE/nix-support" > /dev/null ||
    abort "$BASE/nix-support not found in NIX_PATH; try using run-benchmarks.sh"

# Check as many pre-conditions as we can here
for CMD in annotateDb build-env cabal cabal2nix cluster dump-format \
           dump-package dump-package-env dump-package-name jq mlspec-bench \
           nix-shell runAstPlugin
do
    command -v "$CMD" > /dev/null ||
        abort "Benchmarking needs '$CMD'; maybe add a buildInput to shell.nix?"
done

CACHE=$("$BASE/scripts/cacheDir.sh")

[[ -n "$REPETITIONS" ]] || REPETITIONS=2

info "Benchmarking '$REPETITIONS' packages"

COUNT=0
while read -r LINE
do
    [[ "$COUNT" -lt "$REPETITIONS" ]] || {
        info "Successfully processed '$COUNT' packages; stopping"
        break
    }
    PKG=$(echo "$LINE" | cut -f 1)
    VERSION=$(echo "$LINE" | cut -f 2)
    info "Benchmarking '$PKG'"
    if ! DIR=$("$BASE/scripts/fetchIfNeeded.sh" "$PKG")
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
        CLUSTERS_TODO=$("$BASE/clusterCount.sh")
        while read -r CLUSTERS
        do
            "$BASE/benchmarks/benchmark-cluster.sh"  "$DIR" "$CLUSTERS" &&
            "$BASE/benchmarks/benchmark-explore.sh"  "$DIR" "$CLUSTERS" &&
            "$BASE/benchmarks/benchmark-simplify.sh" "$DIR" "$CLUSTERS" &&
            CLUSTERS_TODO=$(( CLUSTERS_TODO - 1 ))
        done < <("$BASE/scripts/clusterNums.sh")
        [[ "$CLUSTERS_TODO" -eq 0 ]] &&
            COUNT=$(( COUNT + 1 ))   &&
            echo "$DIR" >> "$CACHE/finished"
    fi
done < <("$BASE/scripts/shufflePackages.sh")
