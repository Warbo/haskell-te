#!/bin/sh

# Cluster the features extracted by TreeFeatures

if [ "$#" -lt 1 ]
then
    echo "Please provide a source of features"
    exit 1
fi

SOURCE=$1

function getNames {
    find "$SOURCE" -type f | sort
}

function getCsv {
    getNames | while read LINE
               do
                   cat "$LINE"
               done
}

function elemCount {
    getCsv
    NUMS=$(getCsv | head -n 1 | tr -d -c "," | tr | awk '{ print length; }' | wc -m)
    echo "Nums $NUMS"
    #for (( ; ; expr3 ))
    #do
    #for i in {1..$NUMS}
    #do
    #    echo "."
    #done
}

function getArff {
    echo "@relation empty"
    echo "% NAMES"
    getNames | sed -e 's/^/% /' file
    echo "% /NAMES"
    DATA=$(getCsv)
    echo "$DATA" | tail -n 1 | tr -d -c ',\n' | awk '{ print length; }'
    echo "@data"
}

function runWeka {
    # FIXME: Use stdio
    weka-cli weka.filters.unsupervised.attribute.AddCluster \
             -W "weka.clusterers.SimpleKMeans -N n -S 42" -I last
    # < temp3.arff > out.arff
    #tail -n +37 out.arff > out_bis.arff
    #weka-cli weka.attributeSelection.CfsSubsetEval -M \
    #     -s "weka.attributeSelection.BestFirst -D 1 -N 5" < temp3.arff
}

function showClusters {
    | grep -v "@" |
}

elemCount

#getCsv | runWeka
