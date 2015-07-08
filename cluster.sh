#! /usr/bin/env nix-shell
#! nix-shell -p weka-cli -p jq -p bash -i bash

set -e

# Cluster the features extracted by TreeFeatures

INLINES=$(cat)
CSV=""

function getCsv {
    if [ -z "$CSV" ]
    then
        CSV=$(echo "$INLINES" | jq -r -c '.[] | .features')
    fi
    echo "$CSV"
}

function elemCount {
    # Count the commas in the first row and add 1
    # TODO: Use JSON arrays for features
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
    INPUT=$(cat)
    echo "$INPUT" |
        weka-cli weka.filters.unsupervised.attribute.AddCluster \
                 -W "weka.clusterers.SimpleKMeans -N $CLUSTERS -S 42" -I last
}

function showClusters {
    getArff | runWeka
}

function extractClusters {
    # Chop the final "clusterX" column off the Weka output
    LINES=$(getArff | wc -l)

    showClusters                  |
        grep -A "$LINES" "^@data" |
        grep -o "cluster[0-9]*$"  |
        jq -R '.'                 |
        jq -s --argfile asts <(echo "$INLINES") \
           '. | to_entries | map($asts[.key] + {cluster: .value})'
}

# Reduce an array of ASTs into an object {cluster1: [...], cluster2: [...], ...}
# Then convert that into an array of clusters (since the keys are meaningless)
extractClusters | jq 'reduce .[] as $ast ({}; .[$ast.cluster] += [$ast]) | [.[]]'
