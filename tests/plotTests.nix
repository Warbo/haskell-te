defs: with defs;
with builtins;
with lib;

if plots == null
   then trace "Skipping plot tests, as there are no plots" true
   else all (n: testMsg (checkPlot plots."${n}")
                        "Checking plot ${n}")
            [
              "plotEqsVsTimeForClusters"
              "plotEqsVsTimeForSizes"

              "plotEqsVsClustersForTimes"
              "plotEqsVsSizeForTimes"

              "plotTimeVsClustersForEqs"
              "plotTimeVsSizeForEqs"
            ]
