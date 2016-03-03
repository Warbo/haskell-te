#!/usr/bin/env bash

# Benchmark ML4HS compared to GHC and QuickSpec

function pkgList {
    echo "list-extras"
}

function clusterList {
    seq 1 10
}

function benchmarkGhc {
    cabal get
    cabal configure
    benchmark cabal build
}

function benchmarkOneTimeCost {
    cabal configure with AstPlugin
    benchmark cabal build
    benchmark annotatedb
}

function benchmarkRecurrentClustering {
    while read -r CLUSTERS
    do
        benchmark recurrent clustering into CLUSTERS
    done
}

function benchmarkExploration {
    while read -r CLUSTERS
    do
        benchmark explore-theories with CLUSTERS
    done < <(clusterList)
}

function benchmarkSimplification {
    while read -r CLUSTERS
    do
        benchmark simplify equations from CLUSTERS output
    done < <(clusterList)
}

for PKG in pkgList
do
    benchmarkGhc                 "$PKG"
    benchmarkOneTimeCost         "$PKG"
    benchmarkRecurrentClustering "$PKG"
    benchmarkExploration         "$PKG"
    benchmarkSimplification      "$PKG"
done
