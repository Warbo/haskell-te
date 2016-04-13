{ check, defaultClusters, parseJSON, plotResults, runScript, tabulate }:
with builtins;

let quick = trace "FIXME: Take 'quick' from environment" true; in

with plotResults;
with tabulate { clusters = defaultClusters; inherit quick; };

let

clusters = map toString defaultClusters;

pkgList  = trace "FIXME: Use shuffled list" [ "list-extras" "split" ];

plots    = {

# Equations vs time, for fixed "sizes" (cluster count, cluster size, arguments)
plotEqsVsTimeForClusters = addErrorContext
  "Plotting EqsVsTimeForClusters"
  (scatterPlot (eqsVsTimeForClusters clusters pkgList));

plotEqsVsTimeForSizes    = addErrorContext
  "Plotting EqsVsTimeForSizes"
  (scatterPlot (eqsVsTimeForSizes    clusters pkgList));

plotEqsVsTimeForArgs     = addErrorContext
  "Plotting EqsVsTimeForArgs"
  (scatterPlot (eqsVsTimeForArgs     clusters pkgList));

# Equations vs "size", in a given amount of time
plotEqsVsClustersForTimes = addErrorContext
  "Plotting EqsVsClustersForTimes"
  (scatterPlot (eqsVsClustersForTimes clusters pkgList));

plotEqsVsSizeForTimes     = addErrorContext
  "Plotting EqsVsSizeForTimes"
  (scatterPlot (eqsVsSizeForTimes     clusters pkgList));

plotEqsVsArgsForTimes     = addErrorContext
  "Plotting EqsVsArgsForTimes"
  (scatterPlot (eqsVsArgsForTimes     clusters pkgList));

# Time vs "size", for a given number of equations
plotTimeVsClustersForEqs = addErrorContext
  "Plotting TimeVsClustersForEqs"
  (scatterPlot (timeVsClustersForEqs clusters pkgList));

plotTimeVsSizeForEqs     = addErrorContext
  "Plotting TimeVsSizeForEqs"
  scatterPlot (timeVsSizeForEqs     clusters pkgList);

plotTimeVsArgsForEqs     = addErrorContext
  "Plotting TimeVsArgsForEqs"
  scatterPlot (timeVsArgsForEqs     clusters pkgList);

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
