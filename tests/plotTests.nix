defs: with defs;
with lib;

all (n: testMsg (checkPlot (plots { quick = true; }).${n})
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
