#! /usr/bin/env nix-shell
#! nix-shell -p weka-cli -p bash -i bash

# Cluster the features extracted by TreeFeatures

INLINES=$(cat)

echo "INLINES"  > /dev/stderr
echo "$INLINES" > /dev/stderr

NAMES=""
CSV=""

function getNames {
    if [ -z "$NAMES" ]
    then
        NAMES=$(echo "$INLINES" | cut -d ' ' -f 1)
    fi
    echo "getNames" > /dev/stderr
    echo "$NAMES"   > /dev/stderr
    echo "$NAMES"
}

function getCsv {
    if [ -z "$CSV" ]
    then
        CSV=$(echo "$INLINES" | cut -d ' ' -f 2-)
    fi
    echo "getCsv" > /dev/stderr
    echo "$CSV"   > /dev/stderr
    echo "$CSV"
}

function elemCount {
    # Count the commas in the first row and add 1
    NUMS=$(getCsv | head -n 1 | sed -e 's/[^,]//g' | awk '{ print length; }')
    echo "elemCount" > /dev/stderr
    echo $(($NUMS + 1)) > /dev/stderr
    echo $(($NUMS + 1))
}

function getArff {
    # The data is currently unrelated
    echo "@relation empty"

    # Type annotations for columns (they're all real numbers)
    COUNT=$(elemCount)
    echo "getArff" > /dev/stderr
    echo "$COUNT"  > /dev/stderr
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
    INPUT=$(cat)
    echo "runWeka" > /dev/stderr
    echo "$INPUT"  > /dev/stderr
    echo "$INPUT" |
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
