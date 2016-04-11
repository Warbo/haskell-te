{ lib, processPackages }:
with builtins;
with lib;

{ clusters, quick }:
let processedPackages = processPackages { inherit clusters; } { inherit quick; };
in rec {
    xVsYForZ = x: y: z: data:
      addErrorContext "Tabulating '${x}' vs '${y}' for values of '${z}'" (let

      # Pull out the required data, and give generic labels (x, y, z)
      points = map (p: { x = p."${x}"; y = p."${y}"; z = p."${z}"; }) data;

      # Get all of the possible y values and sort them, to get our axis values
      axisVals = map (p: p.x) points;
      axis     = unique (sort (a: b: a < b) axisVals);

      # Find the values of z we have
      series = unique (map (p: p.z) points);

      # Generate a matrix (list of rows)
      matrix = map (v: map (findCell v) series) axis;

      # Returns the value from the given series at the given axis point;
      # missing data points become "-"
      findCell = v: series: let
         # Those points which match v and series
         ps = filter (p: p.z == series && p.x == v) points;
         # The corresponding y values for these points, if any
         vals = p.map  (p: p.y)      ps;
      in if length vals == []
            then ["-"]
            else vals;

        header = map (series: "${label}{series}") series;
     in { inherit axis header matrix; });

  eqsVsTimeForClusters =
    /*seriess: map (pkg: addErrorContext
    "Tabulating '${pkg}' equations against time for various cluster counts"
    (eqsVsTime "Clusters" { y = "eqs"; x = "withTime"; } seriess
               processedPackages."${pkg}".byClusterSize));*/

               xVsYForZ "eqCount" "withTime" "size";

  eqsVsTimeForSizes    = addErrorContext
    "Tabulating equations against time for various sig sizes"
    (eqsVsTime "Size");

  eqsVsTimeForArgs     = addErrorContext
    "Tabulating equations against time for various arg counts"
    (eqsVsTime "ArgCount");

  eqsVsSize = trace "FIXME: Not implemented" (x: y: z: {
    matrix = [["1" "2"]];
    header = ["x" "y" "z"];
    axis   = ["1"];
  });

  eqsVsClustersForTimes = addErrorContext
    "Tabulating equations against cluster count for various time periods"
    (eqsVsSize "Clusters");

  eqsVsSizeForTimes     = addErrorContext
    "Tabulating equations against sig size for various time periods"
    (eqsVsSize "Size");

  eqsVsArgsForTimes     = addErrorContext
    "Tabulating equations against arg count for various time periods"
    (eqsVsSize "ArgCount");

  timeVsSize = trace "FIXME: Not implemented" (x: y: z: {
      matrix = [["1" "2"]];
          header = ["x" "y" "z"];
              axis   = ["1"];
                });

  timeVsClustersForEqs = addErrorContext
    "Tabulating time against cluster count for various equation counts"
    (timeVsSize "Clusters");

  timeVsSizeForEqs     = addErrorContext
    "Tabulating time against sig size for various equation counts"
    (timeVsSize "Size");

  timeVsArgsForEqs     = addErrorContext
    "Tabulating time against arg counts for various equation counts"
    (timeVsSize "ArgCount");

}
