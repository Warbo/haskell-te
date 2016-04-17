{ check, defaultClusters, parseJSON, plotResults, runScript, tabulate }:
with builtins;

let quick = trace "FIXME: Take 'quick' from environment" true; in

with plotResults;

let

clusters     = map toString defaultClusters;

packageNames = trace "FIXME: Use shuffled list" [ "list-extras" "split" ];

tab          = tabulate { inherit quick packageNames;
                          clusters = defaultClusters; };

plots        = with tab; {

# Equations vs time, for fixed "sizes" (cluster count, cluster size, arguments)
plotEqsVsTimeForClusters = addErrorContext
  "Plotting EqsVsTimeForClusters"
  (scatterPlot eqsVsTimeForClusters);

plotEqsVsTimeForSizes    = addErrorContext
  "Plotting EqsVsTimeForSizes"
  (scatterPlot eqsVsTimeForSizes);

plotEqsVsTimeForArgs     = addErrorContext
  "Plotting EqsVsTimeForArgs"
  (scatterPlot eqsVsTimeForArgs);

# Equations vs "size", in a given amount of time
plotEqsVsClustersForTimes = addErrorContext
  "Plotting EqsVsClustersForTimes"
  (scatterPlot eqsVsClustersForTimes);

plotEqsVsSizeForTimes     = addErrorContext
  "Plotting EqsVsSizeForTimes"
  (scatterPlot eqsVsSizeForTimes);

plotEqsVsArgsForTimes     = addErrorContext
  "Plotting EqsVsArgsForTimes"
  (scatterPlot eqsVsArgsForTimes);

# Time vs "size", for a given number of equations
plotTimeVsClustersForEqs = addErrorContext
  "Plotting TimeVsClustersForEqs"
  (scatterPlot timeVsClustersForEqs);

plotTimeVsSizeForEqs     = addErrorContext
  "Plotting TimeVsSizeForEqs"
  (scatterPlot timeVsSizeForEqs);

plotTimeVsArgsForEqs     = addErrorContext
  "Plotting TimeVsArgsForEqs"
  (scatterPlot timeVsArgsForEqs);

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

in

assert check "Forcing plots" (all (x: assert check "Forcing ${x}"
                                             (isString "${plots.${x}}");
                                      true)
                                  (attrNames plots));

assert check "Ensuring plots are files"
             (all (x: assert check "Checking ${x} is a file"
                                   (isFile plots.${x});
                      true)
                  (attrNames plots));

plots
