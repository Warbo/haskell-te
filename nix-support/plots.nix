{ defaultClusters, plotResults, tabulate }:
with builtins;
with plotResults;
with tabulate;

let clusters = map toString defaultClusters;
    pkgList  = trace "FIXME: Use shuffled list" [ "list-extras" "split" ];
 in {

# Equations vs time, for fixed "sizes" (cluster count, cluster size, arguments)
plotEqsVsTimeForClusters = addErrorContext
  "Plotting EqsVsTimeForClusters"
  (scatterPlot (eqsVsTimeForClusters clusters pkgList));

plotEqsVsTimeForSizes    = addErrorContext
  "Plotting EqsVsTimeForSizes   "
  (scatterPlot (eqsVsTimeForSizes    clusters pkgList));

plotEqsVsTimeForArgs     = addErrorContext
  "Plotting EqsVsTimeForArgs    "
  (scatterPlot (eqsVsTimeForArgs     clusters pkgList));

# Equations vs "size", in a given amount of time
plotEqsVsClustersForTimes = addErrorContext
  "Plotting EqsVsClustersForTimes"
  (scatterPlot (eqsVsClustersForTimes clusters pkgList));

plotEqsVsSizeForTimes     = addErrorContext
  "Plotting EqsVsSizeForTimes    "
  (scatterPlot (eqsVsSizeForTimes     clusters pkgList));

plotEqsVsArgsForTimes     = addErrorContext
  "Plotting EqsVsArgsForTimes    "
  (scatterPlot (eqsVsArgsForTimes     clusters pkgList));

# Time vs "size", for a given number of equations
plotTimeVsClustersForEqs = addErrorContext
  "Plotting TimeVsClustersForEqs"
  (scatterPlot (timeVsClustersForEqs clusters pkgList));

plotTimeVsSizeForEqs     = addErrorContext
  "Plotting TimeVsSizeForEqs    "
  scatterPlot (timeVsSizeForEqs     clusters pkgList);

plotTimeVsArgsForEqs     = addErrorContext
  "Plotting TimeVsArgsForEqs    "
  scatterPlot (timeVsArgsForEqs     clusters pkgList);

}
