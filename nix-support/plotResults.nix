{ gnuplot, lib, runScript, storeResult, withNix, writeScript }:
with builtins;
with lib;

let clusteringData = writeScript "clustering-data" ''
      echo -e "Clusters\tTime"
      while read -r FILE
      do
        CLUSTER=$(echo "$FILE" | grep -o "/[0-9]*-clusters/" | grep -o "[0-9]*")
        MEAN=$(jq '.[] | .reportAnalysis | .anMean | .estPoint' < "$FILE")
        echo -e "$CLUSTER\t$MEAN"
      done < <(find "$CACHE/benchmarks/cluster" -name "*.json")
    '';

    overheadData = writeScript "overhead-data" ''
      set -e

      function timeFor {
        DIR="$CACHE/benchmarks/$2/$1"
        if [[ -d "$DIR" ]]
        then
          for FILE in "$DIR/outputs"/*.json
          # */
          do
            jq '.[] | .reportAnalysis | .anMean | .estPoint' < "$FILE"
            return
          done
        fi
        echo "-"
      }

      function pkgsWith {
        for DIR in "$CACHE/benchmarks/$1"/*
        # */
        do
          basename "$DIR"
        done
      }

      function pkgsWithOverhead {
        printf '%s\n%s\n%s' "$(pkgsWith ghc)"  \
                            "$(pkgsWith dump)" \
                            "$(pkgsWith annotate)" | sort -u | grep -v "^$"
      }

      while read -r PKG
      do
        GHC=$(timeFor "$PKG" ghc)
        DUMP=$(timeFor "$PKG" dump)
        ANNOTATION=$(timeFor "$PKG" annotate)
        printf 'Package\tGHC\tExtraction\tAnnotation\n'
        printf '%s\t%s\t%s\n' "$PKG" "$GHC" "$DUMP" "$ANNOTATION"
      done < <(pkgsWithOverhead)
    '';

    plotOverhead = runScript {} ''
      "${overheadData}" > ./data
      gnuplot -e "filename='data';ofilename='plot.png'" "${bars}"
    '';

    bars = writeScript "bars.gnuplot" ''
      set terminal pngcairo font "arial,10" size 500,500
      set output ofilename

      set boxwidth 0.75 absolute
      set style fill solid 1.00 border -1
      set style data histogram
      set style histogram cluster gap 1
      set xtics rotate by -90

      set title "ML4HS overhead compared to GHC"
      set ylabel "Total time (seconds)"
      set xlabel "Package"

      plot filename using 2:xtic(1) title col, \
                ''' using 3:xtic(1) title col, \
    '';

    plotClustering = runScript {} ''
      "${clusteringData}" > ./data
      gnuplot -e "filename='data';ofilename='plot.png'" "${plot}"
    '';

    plot = writeScript "plot.gnu" ''
      set terminal png
      set output ofilename
      set yrange [0:*]
      plot filename using 1:2 with points
    '';

    mkTbl = keyAttrs: dataAttrs:
      let joinCells = concatStringsSep "\t";
          joinRows  = concatStringsSep "\n";
          mkRow     = _: data: map (key: data."${key}") keys;

          keys = map (a: a.key)  keyAttrs;

          head = joinCells (map (a: a.name) keyAttrs);

          tblA = mapAttrs mkRow dataAttrs;
          tblL = map (n: joinCells tblA."${n}") (attrNames tblA);
       in joinRows ([head] ++ tblL);

    sizeVsThroughputGnus = writeScript "size-vs-throughput.gnu" ''
      set terminal png
      set output ofilename
      set yrange [0:*]
      plot filename using 2:3 with points
    '';

    plotSizeVsThroughput = label: data:
      let fields = [ { name = "Label";      key = "label";      }
                     { name = label;        key = "size";       }
                     { name = "Throughput"; key = "throughput"; } ];
          tbl    = toFile "size-vs-throughput" (mkTbl fields data);
      in runScript (withNix { buildInputs = [ gnuplot ]; }) ''
           set -e
           DATA="${tbl}"
           gnuplot -e "filename='$DATA';ofilename='plot.png'" \
                      "${sizeVsThroughputGnus}"
           "${storeResult}" "plot.png" "$out"
         '';

in { inherit mkTbl plotOverhead plotClustering plotSizeVsThroughput; }
