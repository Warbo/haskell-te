defs: with defs;
with builtins;
with lib;

listToAttrs (map (n: testWrap [ (checkPlot plots."${n}") ]
                              "Checking plot ${n}")
  (if plots == null
      then trace "Skipping plot tests, as there are no plots" []
      else map
               [ "plotEqsVsTimeForClusters"
                 "plotEqsVsTimeForSizes"

                 "plotEqsVsClustersForTimes"
                 "plotEqsVsSizeForTimes"

                 "plotTimeVsClustersForEqs"
                 "plotTimeVsSizeForEqs"
               ])
}
