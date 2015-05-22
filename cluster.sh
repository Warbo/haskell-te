#!/bin/sh

# Cluster the features extracted by TreeFeatures

if [ "$#" -lt 2 ]
then
    echo "Please provide a source of features"
    exit 1
fi

SOURCE=$1

function getCsv {
    for PKG in "$SOURCE"
    do
        for MOD in "$SOURCE/$PKG"
        do
            for NAME in "$SOURCE/$PKG/$MOD"
            do
                cat "$SOURCE/$PKG/$MOD/$NAME"
            done
        done
    done
}

function runWeka {
    # FIXME: Use stdio
    weka-cli weka.filters.unsupervised.attribute.AddCluster \
         -W "weka.clusterers.ALG -N n -S 42" -I last < temp3.arff > out.arff
    tail -n +37 out.arff > out_bis.arff
    weka-cli weka.attributeSelection.CfsSubsetEval -M \
         -s "weka.attributeSelection.BestFirst -D 1 -N 5" < temp3.arff
}

getCsv | runWeka
