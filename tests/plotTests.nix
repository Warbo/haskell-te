defs: with defs;
with builtins;
with lib;

plots != null &&
all (n: testMsg (checkPlot plots.${n})
                "Checking plot ${n}")
    [
      "plotEqsVsTimeForClusters"
      "plotEqsVsTimeForSizes"
      "plotEqsVsTimeForArgs"

      "plotEqsVsClustersForTimes"
      "plotEqsVsSizeForTimes"
      "plotEqsVsArgsForTimes"

      "plotTimeVsClustersForEqs"
      "plotTimeVsSizeForEqs"
      "plotTimeVsArgsForEqs"
    ]
