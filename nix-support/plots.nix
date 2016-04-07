{ defaultClusters, plotResults, tabulate }:
with builtins;
with plotResults;
with tabulate;

let clusters = map toString defaultClusters;
    pkgList  = trace "FIXME: Use shuffled list" [ "list-extras" "split" ];
 in {

plotEqsVsTimeForKs = scatterPlot (eqsVsTimeForKs clusters pkgList);

}
