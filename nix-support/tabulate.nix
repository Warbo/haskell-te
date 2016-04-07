{ lib, processedPackages }:
with builtins;
with lib;

rec {
    eqsVsTime = label: seriess: pkgNames:
    # For each series, construct a list of points {x, y} where x is the time and
    # y is the equation count.
    let points = listToAttrs (map (series: {
                                    name  = series;
                                    value = map (name: {
                                                  y = processedPackages."${name}".equationCount."${series}";
                                                  x = processedPackages."${name}".totalWithTime."${series}";
                                                })
                                                pkgNames;
                                  })
                                  seriess);
        # Get all of the possible y values and sort them
        axisVals = concatMap (series: map (p: p.y)
                                          points."${series}")
                             seriess;
        axis     = unique (sort (a: b: a < b) axisVals);

        # Generate a matrix (list of rows)
        matrix = map (v: map (findCell v) seriess) axis;

        # Returns the value from the given series at the given axis point;
        # missing data points become "-"
        findCell = v: series:
          let ps   = filter (p: p.y == v) points."${series}";
              vals = map    (p: p.y)      ps;
           in head (vals ++ ["-"]);

        header = ["Equations"] ++ map (series: "${label}{series}") seriess;
     in { inherit axis header matrix; };

  eqsVsTimeForClusters = addErrorContext
    "Tabulating equations against time for various cluster counts"
    (eqsVsTime "Clusters");

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
