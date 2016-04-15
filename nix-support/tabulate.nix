{ check, checkTime, lib, processPackages }:
with builtins;
with lib;

{ clusters, quick, packageNames }:
let

looksNumeric = x: any id [
  (isInt    x -> checkNumeric x)
  (isString x -> checkNumeric x)
  (isAttrs  x -> checkTime    x)
];

checkNumeric = x: "" == replaceStrings
                          ["0" "1" "2" "3" "4" "5" "6" "7" "8" "9" "."]
                          [""  ""  ""  ""  ""  ""  ""  ""  ""  ""  "" ]
                          (toString x);

compareAsInts = a: b:
  let aI = fromJSON (toString a);
      bI = fromJSON (toString b);
   in assert check "Argument ${toJSON a} became int ${toJSON aI}" (isInt aI);
      assert check "Argument ${toJSON b} became int ${toJSON bI}" (isInt bI);
      aI < bI;

processedPackages = processPackages { inherit clusters; } { inherit quick; };

collectData = field:
  assert check "Field is string ${toJSON field}" (isString field);
  assert check "Package names are strings" (all isString packageNames);
  fold (name: old: old ++ processedPackages.${name}.${field})
       []
       packageNames;

# Each data point is a particular cluster
dataBySize         = collectData "sizeDataPoints";

# Each data point is a package split into k clusters
dataByClusterCount = collectData "clusterDataPoints";

preConditions = x: y: z: data: all id [

  (check "Field names are strings" (all isString [x y z]))

  (check "Forcing data" (isString "${toJSON data}"))

  (check "isList data (${typeOf data})" (isList data))

  (check "Data contains sets"
         (all (p: check "isAttrs ${toJSON p}"
                        (isAttrs p))
              data))

  (check "Points have ${x}" (all (p: check "Has ${x} ${toJSON p}"
                                           (p ? ${x}))
                                 data))

  (check "Points have ${y}" (all (p: check "Has ${y} ${toJSON p}"
                                           (p ? ${y}))
                                 data))

  (check "Points have ${z}" (all (p: check "Has ${z} ${toJSON p}"
                                           (p ? ${z}))
                            data))

  (check "Can sort ${x}" (all (p: check "checkNumeric ${toJSON p.${x}}"
                                        (checkNumeric p.${x}))
                              data))

  (check "${y} looks numeric" (all (p: check "Looks numeric ${toJSON p.${y}}"
                                             (looksNumeric p.${y}))
                                   data))

  (check "${z} looks numeric" (all (p: check "Looks numeric ${toJSON p.${z}}"
                                             (looksNumeric p.${z}))
                                   data))

];

postConditions = result: all id [

  (check "isList axis (${typeOf result.axis})"     (isList result.axis))

  (check "isList matrix (${typeOf result.matrix})" (isList result.matrix))

  (check "Matrix is 2D" (all (x: check "isList ${toJSON x}" (isList x))
                             result.matrix))

  (check "Forcing components of result"
         (all (x: check "Forcing field ${x}"
                        (isString "${toJSON result.${x}}"))
              (attrNames result)))

  (check "Force result" (isString "${toJSON result}"))

];

# Wrap our tabulation function in a load of assertions, since there is a lot of
# room for errors which may slip through unnoticed (e.g. one int looks just like
# another).
xVsYForZ = x: y: z: data:
  let result = addErrorContext "Tabulating ${x} vs ${y} for values of ${z}"
                               (xVsYForZReal x y z data);
   in assert check "Pre-conditions for ${x} vs ${y} per ${z}"
                   (preConditions x y z data);
      assert check "Post-conditions for ${x} vs ${y} per ${z}"
                   (postConditions result);
      result;

# Performs the actual tabulation of fields
xVsYForZReal = x: y: z: data:
  let # Pull out the required data, and give generic labels (x, y, z)
      points = map (p: { x = p.${x}; y = p.${y}; z = p.${z}; }) data;

      # Get all of the possible y values and sort them, to get our axis values
      axisVals = map (p: p.x) points;
      axis     = unique (sort compareAsInts axisVals);

      # Find the values of z we have
      series = unique (map (p: p.z) points);

      # Generate a matrix (list of rows)
      matrix = map (v: map (findCell v) series) axis;

      # Returns the value from the given series at the given axis point;
      # missing data points become "-"
      findCell = v: series:
        let # Those points which match v and series
            ps = filter (p: p.z == series && p.x == v) points;
            # The corresponding y values for these points, if any
            vals = map (p: p.y) ps;
         in if length vals == []
               then ["-"]
               else vals;

      header = map toString series;

   in { inherit axis header matrix; };

tabulated = listToAttrs
  (map ({ x, y, z, data, name }:
          addErrorContext "Tabulating ${x} vs ${y} for ${z}" {
            inherit name;
            value = xVsYForZ x y z data;
          })
       [
         {
           name = "eqsVsTimeForClusters";
           x    = "eqCount";
           y    = "totalTime";
           z    = "clusterCount";
           data = dataByClusterCount;
         }

         {
           name = "eqsVsTimeForSizes";
           x    = "eqCount";
           y    = "totalTime";
           z    = "size";
           data = dataBySize;
         }

         {
           name = "eqsVsTimeForArgs";
           x    = "eqCount";
           y    = "totalTime";
           z    = "argCount";
           data = dataBySize;
         }

         {
           name = "eqsVsClustersForTimes";
           x    = "eqCount";
           y    = "clusterCount";
           z    = "timeBucket";
           data = dataByClusterCount;
         }

         {
           name = "eqsVsSizeForTimes";
           x    = "eqCount";
           y    = "size";
           z    = "timeBucket";
           data = dataBySize;
         }

         {
           name = "eqsVsArgsForTimes";
           x    = "eqCount";
           y    = "argCount";
           z    = "timeBucket";
           data = dataBySize;
         }

         {
           name = "timeVsClustersForEqs";
           x    = "clusterCount";
           y    = "totalTime";
           z    = "eqCount";
           data = dataByClusterCount;
         }

         {
           name = "timeVsSizeForEqs";
           x    = "size";
           y    = "totalTime";
           z    = "eqCount";
           data = dataBySize;
         }

         {
           name = "timeVsArgsForEqs";
           x    = "argCount";
           y    = "totalTime";
           z    = "eqCount";
           data = dataBySize;
         }

       ]);

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

assert check "Checking tabulate output" (all id [

  (check "isAttrs tabulated (${typeOf tabulated})" (isAttrs tabulated))

  (check "tabulated contains sets"
         (all (t: check "isAttrs ${typeOf tabulated.${t}}"
                        (isAttrs tabulated.${t}))
              (attrNames tabulated)))

  (check "Forcing tabulated results"
         (all (n: check "Forcing ${n}"
                        (isString "${toJSON tabulated.${n}}"))
              (attrNames tabulated)))

]);

tabulated
