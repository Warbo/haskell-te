{ lib, processedPackages }:
with builtins;
with lib;

rec {
  eqsVsTimeForKs = clusters: pkgNames:
    # For each number of clusters, construct a list of points {x, y} where x is
    # the time and y is the equation count.
    let points = listToAttrs (map (cluster: {
                                    name  = cluster;
                                    value = map (name: {
                                                  y = processedPackages."${name}".equationCount."${cluster}";
                                                  x = processedPackages."${name}".totalWithTime."${cluster}";
                                                })
                                                pkgNames;
                                  })
                                  clusters);
        # Get all of the possible y values and sort them
        axisVals = concatMap (c: map (p: p.y)
                                     points."${c}")
                             clusters;
        axis     = sort (a: b: a < b) axisVals;

        # Generate a matrix (list of rows)
        matrix = map (v: map (findCell v) clusters) axis;

        # Returns the value from the given cluster at the given axis point;
        # missing data points become "-"
        findCell = v: cluster:
          let ps   = filter (p: p.y == v) points."${cluster}";
              vals = map    (p: p.y)      ps;
           in head (vals ++ ["-"]);

        header = ["Equations"] ++ map (c: "${c} clusters") clusters;
     in { inherit axis header matrix; };
}
