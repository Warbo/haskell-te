{ doCheck, defaultClusters, lib, parseJSON, plotResults, runScript, shuffledList,
  tabulate }:
with builtins;
with lib;

let quick = trace "FIXME: Take 'quick' from environment" true; in

with plotResults;

let

count        = if getEnv "PLOT_COUNT" == ""
                  then 1
                  else fromJSON (getEnv "PLOT_COUNT");

clusters     = map toString defaultClusters;

tab          = tabulate {
                 inherit count quick;
                 clusters     = defaultClusters;
                 packageNames = take 1 shuffledList;
               };

plots        = with tab; trace "plots: tab=${toJSON tab}" {

# Equations vs time, for fixed "sizes" (cluster count, cluster size, arguments)
plotEqsVsTimeForClusters = addErrorContext
  "Plotting EqsVsTimeForClusters"
  (scatterPlot eqsVsTimeForClusters);

plotEqsVsTimeForSizes    = addErrorContext
  "Plotting EqsVsTimeForSizes"
  (scatterPlot eqsVsTimeForSizes);

# Equations vs "size", in a given amount of time
plotEqsVsClustersForTimes = addErrorContext
  "Plotting EqsVsClustersForTimes"
  (scatterPlot eqsVsClustersForTimes);

plotEqsVsSizeForTimes     = addErrorContext
  "Plotting EqsVsSizeForTimes"
  (scatterPlot eqsVsSizeForTimes);

# Time vs "size", for a given number of equations
plotTimeVsClustersForEqs = addErrorContext
  "Plotting TimeVsClustersForEqs"
  (scatterPlot timeVsClustersForEqs);

plotTimeVsSizeForEqs     = addErrorContext
  "Plotting TimeVsSizeForEqs"
  (scatterPlot timeVsSizeForEqs);

};

isFile = f: parseJSON (runScript {} ''
    set -e
    echo "Checking if '${f}' exists" 1>&2
    [[ -f "${f}" ]] || {
      echo "Couldn't find file '${f}'" 1>&2
      exit 2
    }
    echo "true" > "$out"
  '');

haveData = !(any (n: tab."${n}".series == {})
                 (attrNames tab));

in

if haveData
   then assert doCheck "Forcing plots" (all (x: assert doCheck "Forcing ${x}"
                                                           (isString "${plots.${x}}");
                                              true)
                                          (attrNames plots));

        assert doCheck "Ensuring plots are files"
                     (all (x: assert doCheck "Checking ${x} is a file"
                                           (isFile plots."${x}");
                              true)
                          (attrNames plots));

        plots
    else null
