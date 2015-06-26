#! /usr/bin/env nix-shell
#! nix-shell -p weka-cli -p bash -i bash

VERBOSE=0

function vDebug {
    test "$VERBOSE" -eq 0 || cat > /dev/stderr
}

# Cluster the features extracted by TreeFeatures

INLINES=$(cat)

echo "INLINES"  | vDebug
echo "$INLINES" | vDebug

NAMES=""
CSV=""

function getNames {
    if [ -z "$NAMES" ]
    then
        NAMES=$(echo "$INLINES" | cut -d ' ' -f 1)
    fi
    echo "getNames" | vDebug
    echo "$NAMES"   | vDebug
    echo "$NAMES"
}

function getCsv {
    if [ -z "$CSV" ]
    then
        CSV=$(echo "$INLINES" | cut -d ' ' -f 2-)
    fi
    echo "getCsv" | vDebug
    echo "$CSV"   | vDebug
    echo "$CSV"
}

function elemCount {
    # Count the commas in the first row and add 1
    NUMS=$(getCsv | head -n 1 | sed -e 's/[^,]//g' | awk '{ print length; }')
    echo "elemCount" | vDebug
    echo $(($NUMS + 1)) | vDebug
    echo $(($NUMS + 1))
}

function getArff {
    # The data is currently unrelated
    echo "@relation empty"

    # Type annotations for columns (they're all real numbers)
    COUNT=$(elemCount)
    echo "getArff" | vDebug
    echo "$COUNT"  | vDebug
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
    echo "runWeka" | vDebug
    echo "$INPUT"  | vDebug
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
