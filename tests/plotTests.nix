defs: with defs;
with builtins;
with lib;

testWrap
  (if plots == null
      then trace "Skipping plot tests, as there are no plots" []
      else map (n: testWrap [ (checkPlot plots."${n}") ]
                           "Checking plot ${n}")
               [ "plotEqsVsTimeForClusters"
                 "plotEqsVsTimeForSizes"

                 "plotEqsVsClustersForTimes"
                 "plotEqsVsSizeForTimes"

                 "plotTimeVsClustersForEqs"
                 "plotTimeVsSizeForEqs"
               ])
  "All plot tests"
