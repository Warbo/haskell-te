defs: with defs;
with lib;
with plots;

testMsg (all checkPlot [
  plotEqsVsTimeForClusters
  plotEqsVsTimeForSizes
  plotEqsVsTimeForArgs

  plotEqsVsClustersForTimes
  plotEqsVsSizeForTimes
  plotEqsVsArgsForTimes

  plotTimeVsClustersForEqs
  plotTimeVsSizeForEqs
  plotTimeVsArgsForEqs
]) "Checking final plots"
