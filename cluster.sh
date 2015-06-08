#!/bin/sh

# Cluster the features extracted by TreeFeatures

test "$#" -lt 1 && echo "Please provide a source of features" && exit 1

SOURCE=$1
NAMES=""
CSV=""

function getNames {
    if [ -z "$NAMES" ]
    then
        NAMES=$(find "$SOURCE" -type f | sort)
    fi
    echo "$NAMES"
}

function getCsv {
    if [ -z "$CSV" ]
    then
        CSV=$(getNames | while read LINE
                         do
                             cat "$LINE"
                         done)
    fi
    echo "$CSV"
}

function elemCount {
    # Count the commas in the first row and add 1
    NUMS=$(getCsv | head -n 1 | sed -e 's/[^,]//g' | awk '{ print length; }')
    echo $(($NUMS + 1))
}

function getArff {
    # The data is currently unrelated
    echo "@relation empty"

    # Type annotations for columns (they're all real numbers)
    COUNT=$(elemCount)
    for (( i=1; i<=$COUNT; i++ ))
    do
        echo "@attribute '$i' real"
    done

    # The data to cluster
    echo "@data"
    getCsv
}

function runWeka {
    CLUSTERS=4
    weka-cli weka.filters.unsupervised.attribute.AddCluster \
             -W "weka.clusterers.SimpleKMeans -N $CLUSTERS -S 42" -I last
}

function showClusters {
    getArff | runWeka
    # | grep -v "@"
}

function extractClusters {
    # Chop the final "clusterX" column off the Weka output
    LINES=$(getArff | wc -l)
    CLUSTERS=$(showClusters | grep -A "$LINES" "^@data" | grep -o "cluster[0-9]*$")

    # Interleave with input CSV filenames
    mkfifo fifo
    getNames > fifo &
    echo "$CLUSTERS" | paste - fifo
    rm fifo
}

extractClusters
