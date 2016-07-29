defs: with defs;
with builtins;
with lib;

if plots == null
   then trace "Skipping plot tests, as there are no plots" {}
   else listToAttrs (map (n: { name  = n;
                               value = checkPlot plots."${n}"; })
                         [ "plotEqsVsTimeForClusters"
                           "plotEqsVsTimeForSizes"

                           "plotEqsVsClustersForTimes"
                           "plotEqsVsSizeForTimes"

                           "plotTimeVsClustersForEqs"
                           "plotTimeVsSizeForEqs"
                         ])
