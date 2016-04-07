{ lib, processedPackages }:
with builtins;
with lib;

rec {
  eqsVsTimeForKs = clusters: pkgNames:
    # Each column is a cluster number
    let points = listToAttrs (map (cluster: {
                                    name  = cluster;
                                    value = map (name: {
                                                  eqs  = processedPackages."${name}".equationCount."${cluster}";
                                                  time = processedPackages."${name}".totalWithTime."${cluster}";
                                                })
                                                pkgNames;
                                  })
                                  clusters);
        # Choose one column for an axis, get all of its values and sort them
        axisCol  = "eqs";
        axisVals = concatMap (c: map (p: p."${axisCol}")
                                     points."${c}")
                             clusters;
        axis     = sort (x: y: x < y) axisVals;

        # Generate a matrix (list of rows)
        matrix = map (v: map (findCell v) clusters) axis;

        # Returns the value from the given cluster at the given axis point;
        # missing data points become "-"
        findCells = v: cluster:
          let vals = filter (p: p."${axisCol}" == v) points."${cluster}";
           in head (vals ++ ["-"]);

        header = ["Equations"] ++ map (c: "${c} clusters") clusters;
     in { inherit axis header matrix; };
}
