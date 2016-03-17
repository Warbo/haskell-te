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

function pkgInList {
    touch "$CACHE/$2"
    grep -Fx -- "$1" < "$CACHE/$2" > /dev/null
}

COUNT=0
while read -r LINE
do
    # Stop if disk is filling
    SPACE=$(df -h | grep /dev/disk/by-label/nixos | sed -e 's@  *@ @g' | cut -d ' ' -f 5 | sed -e 's@%@@g')
    info "Disk is $SPACE percent full"
    [[ "$SPACE" -gt 98 ]] && abort "Disk full, stopping"

    [[ "$COUNT" -lt "$REPETITIONS" ]] || {
        info "Successfully processed '$COUNT' packages; stopping"
        break
    }
    PKG=$(echo "$LINE" | cut -f 1)
    VERSION=$(echo "$LINE" | cut -f 2)

    # Skip packages which we've already processed
    SKIP=""
    for LIST in finished unfetchable unbuildable unexplorable unquickspecable \
                featureless unclusterable
    do
        if pkgInList "$PKG" "$LIST"
        then
            SKIP="$LIST"
            break
        fi
    done

    if [[ -n "$SKIP" ]]
    then
        info "Skipping '$PKG' as it is $SKIP"
        continue
    fi

    info "Benchmarking '$PKG'"
    if ! DIR=$("$BASE/scripts/fetchIfNeeded.sh" "$PKG")
    then
        unfetchable "$PKG"
        continue
    fi

    if ! "$BASE/benchmarks/benchmark-ghc.sh" "$DIR"
    then
        unbuildable "$PKG"
        continue
    fi

    if ! "$BASE/benchmarks/benchmark-features.sh" "$DIR"
    then
        featureless "$PKG"
        continue
    fi

    # Make sure we run all clusters for this package
    while read -r CLUSTERS
    do
        "$BASE/benchmarks/benchmark-cluster.sh"  "$DIR" "$CLUSTERS" || {
            echo "$PKG" >> "$CACHE/unclusterable"
            continue
        }
        "$BASE/benchmarks/benchmark-explore.sh"  "$DIR" "$CLUSTERS" || {
            echo "$PKG" >> "$CACHE/unexplorable"
            continue
        }
        "$BASE/benchmarks/benchmark-simplify.sh" "$DIR" "$CLUSTERS"
    done < <(clusterNums)

    echo "$PKG" >> "$CACHE/finished"

    #COUNT=$(( COUNT + 1 ))
done < <("$BASE/scripts/shufflePackages.sh")
