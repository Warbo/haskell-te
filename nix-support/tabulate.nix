{ check, lib, processPackages }:
with builtins;
with lib;

{ clusters, quick, packageNames }:
let

processedPackages = processPackages { inherit clusters; } { inherit quick; };

collectData = field: fold (name: old: old ++ processedPackages.${name}.${field})
                          []
                          packageNames;

# Each data point is a particular cluster
dataBySize         = collectData "sizeDataPoints";

# Each data point is a package split into k clusters
dataByClusterCount = collectData "clusterDataPoints";

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
       vals = map (p: p.y) ps;
    in if length vals == []
          then ["-"]
          else vals;

      header = map toString series;
  in { inherit axis header matrix; });

tabulated = {

  eqsVsTimeForClusters = addErrorContext
    "Tabularing equations against time for various cluster counts"
    (xVsYForZ "eqCount" "totalTime" "clusterCount" dataByClusterCount);

  eqsVsTimeForSizes    = addErrorContext
    "Tabulating equations against time for various sig sizes"
    (xVsYForZ "eqCount" "totalTime" "size" dataBySize);

  eqsVsTimeForArgs     = addErrorContext
    "Tabulating equations against time for various arg counts"
    (xVsYForZ "eqCount" "totalTime" "argCount" dataBySize);

  eqsVsClustersForTimes = addErrorContext
    "Tabulating equations against cluster count for various time periods"
    (xVsYForZ "eqCount" "clusterCount" "totalTime" dataByClusterCount);

  eqsVsSizeForTimes     = addErrorContext
    "Tabulating equations against sig size for various time periods"
    (xVsYForZ "eqCount" "size" "totalTime" dataBySize);

  eqsVsArgsForTimes     = addErrorContext
    "Tabulating equations against arg count for various time periods"
    (xVsYForZ "eqCount" "argCount" "totalTime" dataBySize);

  timeVsClustersForEqs = addErrorContext
    "Tabulating time against cluster count for various equation counts"
    (xVsYForZ "totalTime" "clusterCount" "eqCount" dataByClusterCount);

  timeVsSizeForEqs     = addErrorContext
    "Tabulating time against sig size for various equation counts"
    (xVsYForZ "totalTime" "size" "eqCount" dataBySize);

  timeVsArgsForEqs     = addErrorContext
    "Tabulating time against arg counts for various equation counts"
    (xVsYForZ "totalTime" "argCount" "eqCount" dataBySize);

};

in

assert check "Checking tabulate inputs" (all id [

  (check "packageNames is list ${toJSON packageNames}"
         (isList packageNames))

  (check "Package names are strings ${toJSON packageNames}"
         (all isString packageNames))

  (check "'quick' is a boolean ${toJSON quick}" (isBool quick))

]);

assert check "Checking tabulate data" (all id [

  (check "isList dataBySize ${toJSON dataBySize}"
         (isList dataBySize))

  (check "All dataBySize have required fields"
         (all (f: check "All dataBySize have ${f}"
                        (all (p: check "${f} appears in ${toJSON p}"
                                       (p ? ${f}))
                             dataBySize))
              [ "eqCount" "totalTime" "argCount" "size" ]))

  (check "isList dataByClusterCount ${toJSON dataByClusterCount}"
         (isList dataBySize))

  (check "All dataByClusterCount have required fields"
         (all (f: check "All dataByClusterCount have ${f}"
                        (all (p: check "${f} appears in ${toJSON p}"
                                       (p ? ${f}))
                             dataByClusterCount))
              ["eqCount" "totalTime" "clusterCount"]))

]);

assert check "Forcing tabulated results"
             (all (n: assert check "Forcing ${n}"
                                   (isString "${toJSON tabulated.${n}}");
                      true)
                  (attrNames tabulated));

tabulated
