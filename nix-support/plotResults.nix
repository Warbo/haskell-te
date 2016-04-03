{}:

runScript {} ''
function clusteringData {
    echo -e "Clusters\tTime"
    while read -r FILE
    do
        CLUSTER=$(echo "$FILE" | grep -o "/[0-9]*-clusters/" | grep -o "[0-9]*")
        MEAN=$(jq '.[] | .reportAnalysis | .anMean | .estPoint' < "$FILE")
        echo -e "$CLUSTER\t$MEAN"
    done < <(find "$CACHE/benchmarks/cluster" -name "*.json")
}

function timeFor {
    DIR="$CACHE/benchmarks/$2/$1"
    if [[ -d "$DIR" ]]
    then
        for FILE in "$DIR/outputs"/*.json
        do
            jq '.[] | .reportAnalysis | .anMean | .estPoint' < "$FILE"
            return
        done
    fi
    echo "-"
}

function pkgsWith {
    for DIR in "$CACHE/benchmarks/$1"/*
    do
        basename "$DIR"
    done
}

function pkgsWithOverhead {
    printf '%s\n%s\n%s' "$(pkgsWith ghc)"  \
                        "$(pkgsWith dump)" \
                        "$(pkgsWith annotate)" | sort -u | grep -v "^$"
}

function overheadData {
    while read -r PKG
    do
        GHC=$(timeFor "$PKG" ghc)
        DUMP=$(timeFor "$PKG" dump)
        ANNOTATION=$(timeFor "$PKG" annotate)
        printf 'Package\tGHC\tExtraction\tAnnotation\n'
        printf '%s\t%s\t%s\n' "$PKG" "$GHC" "$DUMP" "$ANNOTATION"
    done < <(pkgsWithOverhead)
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
''
