#!/usr/bin/env bash

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
NAME=$(basename "$0")
source "$BASE/scripts/common.sh"

for CMD in jq gnuplot
do
    requireCmd "$CMD"
done

mkdir -p "$CACHE/results"

function clusteringData {
    echo -e "Clusters\tTime"
    while read -r FILE
    do
        CLUSTER=$(echo "$FILE" | grep -o "/[0-9]*-clusters/" | grep -o "[0-9]*")
        MEAN=$(jq '.[] | .reportAnalysis | .anMean | .estPoint' < "$FILE")
        echo -e "$CLUSTER\t$MEAN"
    done < <(find "$CACHE/benchmarks/cluster" -name "*.json")
}

function overheadData {
    # Label Time

    # First, regular GHC
    while read -r FILE
    do
        LABEL=$(echo "$FILE" | sed -e 's@.*homechrisProgramminghaskelltecache@@g' | sed -e 's@.json$@@g')
        MEAN=$(jq '.[] | .reportAnalysis | .anMean | .estPoint' < "$FILE")
        echo -e "GHC-$LABEL\t$MEAN"
    done < <(find "$CACHE/benchmarks/outputs" -name "cabal-build*.json")

    # Now our feature extraction
    while read -r FILE
    do
        LABEL=$(echo "$FILE" | sed -e 's@.*runAstPlugin-@@g' | sed -e 's@.json$@@g')
        MEAN=$(jq '.[] | .reportAnalysis | .anMean | .estPoint' < "$FILE")
        echo -e "AST-$LABEL\t$MEAN"
    done < <(find "$CACHE/benchmarks/outputs" -name "runAstPlugin*.json")
}

function plotClustering {
    DATA_FILE="$CACHE/results/clustering.gnuplotdata"
    clusteringData > "$DATA_FILE"

    PLOT_FILE="$CACHE/results/clustering.png"

    gnuplot -e "filename='$DATA_FILE';ofilename='$PLOT_FILE'" "$BASE/scripts/plot.gnu"
}

function plotOverhead {
    DATA_FILE="$CACHE/results/overhead.gnuplotdata"

    overheadData > "$DATA_FILE"

    PLOT_FILE="$CACHE/results/overhead.png"

    gnuplot -e "filename='$DATA_FILE';ofilename='$PLOT_FILE'" "$BASE/scripts/bars.gnu"
}

plotOverhead
plotClustering
