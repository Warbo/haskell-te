#!/usr/bin/env bash

# Benchmark ML4HS compared to GHC and QuickSpec

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
NAME=$(basename "$0")
source "$BASE/scripts/common.sh"

function unfetchable {
    echo "$1" >> "$CACHE/unfetchable"
    uniqueLines "$CACHE/unfetchable"
}

function unbuildable {
    echo "$1" >> "$CACHE/unbuildable"
    uniqueLines "$CACHE/unbuildable"
}

function featureless {
    echo "$1" >> "$CACHE/featureless"
    uniqueLines "$CACHE/featureless"
}

# Ensure our Nix packages are in use
echo "$NIX_PATH" | grep "$BASE/nix-support" > /dev/null ||
    abort "$BASE/nix-support not found in NIX_PATH; try using run-benchmarks.sh"

# Check as many pre-conditions as we can here
for CMD in annotateDb build-env cabal cabal2nix cluster dump-format \
           dump-package dump-package-env dump-package-name jq mlspec-bench \
           nix-shell runAstPlugin time
do
    requireCmd "$CMD"
done

# Clean out stale/erroneous data from cache
[[ -d "$CACHE" ]] || mkdir -p "$CACHE"

# Remove unparseable times
rm -f "$CACHE"/*.time  # Left-over files
while read -r FILE
do
    jq '.' < "$FILE" > /dev/null || {
        warn "Deleting unparseable benchmark result '$FILE'"
        rm -f "$FILE"
    }
done < <(find "$CACHE/benchmarks" -name "*.json")

# Remove empty results
shopt -s nullglob
while read -r FILE
do
    rm -fv "$FILE"
done < <(find "$CACHE" -maxdepth 1 -empty -type f \( \
              -name "*.annotated" -o -name "*.asts" -o -name "*.formatted.*" \
           -o -name "*.clustered.*" -o -name "*.explored.*" \) )

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
        unfetchable "$PKG"
    elif ! "$BASE/benchmarks/benchmark-ghc.sh" "$DIR"
    then
        unbuildable "$DIR"
    elif ! "$BASE/benchmarks/benchmark-features.sh" "$DIR"
    then
        featureless "$DIR"
    else
        # Make sure we run all clusters for this package
        CLUSTERS_TODO=$(clusterCount)
        while read -r CLUSTERS
        do
            "$BASE/benchmarks/benchmark-cluster.sh"  "$DIR" "$CLUSTERS" &&
            "$BASE/benchmarks/benchmark-explore.sh"  "$DIR" "$CLUSTERS" &&
            "$BASE/benchmarks/benchmark-simplify.sh" "$DIR" "$CLUSTERS" &&
            CLUSTERS_TODO=$(( CLUSTERS_TODO - 1 ))
        done < <(clusterNums)
        [[ "$CLUSTERS_TODO" -eq 0 ]] &&
            COUNT=$(( COUNT + 1 ))   &&
            echo "$DIR" >> "$CACHE/finished"
    fi
done < <("$BASE/scripts/shufflePackages.sh")
