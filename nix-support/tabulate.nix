{ ourCheck, checkTime, lib, processPackages }:
with builtins;
with lib;

{ clusters, count, quick, packageNames }:
let

looksNumeric = x: any id [
  (isInt    x -> checkNumeric x)
  (isString x -> checkNumeric x)
  (isAttrs  x -> checkTime    x)
];

checkNumeric = x: "" == replaceStrings
                          ["0" "1" "2" "3" "4" "5" "6" "7" "8" "9" "."]
                          [""  ""  ""  ""  ""  ""  ""  ""  ""  ""  "" ]
                          (addErrorContext "Checking ${toJSON x} is numeric"
                                           (toString x));

compareAsInts = a: b:
  let aI = addErrorContext "Turning ${toJSON a} into int"
                           (fromJSON (toString a));
      bI = addErrorContext "Turning ${toJSON b} into int"
                           (fromJSON (toString b));
   in assert ourCheck "Argument ${toJSON a} became int ${toJSON aI}" (isInt aI);
      assert ourCheck "Argument ${toJSON b} became int ${toJSON bI}" (isInt bI);
      aI < bI;

processedPackages = processPackages { inherit clusters quick; };

appendData = field: name: { pkgCount, data }:
  let stop   = pkgCount >= count;
      failed = if processedPackages."${name}".failed
                  then trace "Skip failed package '${name}'" true
                  else false;
      output = if stop || failed
                   then { inherit data pkgCount; }
                   else { data     = data ++ processedPackages."${name}"."${field}";
                          pkgCount = pkgCount + 1; };
   in output;

collectData = field:
  assert ourCheck "Field is string ${toJSON field}" (isString field);
  assert ourCheck "Package names are strings" (all isString packageNames);
  (fold (appendData field)
        { pkgCount = 0; data = []; }
        (filter (n: !processedPackages."${n}".failed) packageNames)).data;

# Each data point is a package split into k clusters
dataByClusterCount = collectData "clusterDataPoints";

preConditions = x: y: z: data: all id [

  (ourCheck "Field names are strings" (all isString [x y z]))

  (ourCheck "Forcing data" (isString "${toJSON data}"))

  (ourCheck "isList data (${typeOf data})" (isList data))

  (ourCheck "Data contains sets"
         (all (p: ourCheck "isAttrs ${toJSON p}"
                        (isAttrs p))
              data))

  (ourCheck "Points have ${x}" (all (p: ourCheck "Has ${x} ${toJSON p}"
                                           (p ? "${x}"))
                                 data))

  (ourCheck "Points have ${y}" (all (p: ourCheck "Has ${y} ${toJSON p}"
                                           (p ? "${y}"))
                                 data))

  (ourCheck "Points have ${z}" (all (p: ourCheck "Has ${z} ${toJSON p}"
                                           (p ? "${z}"))
                            data))

  (ourCheck "Can sort ${x}" (all (p: ourCheck "checkNumeric ${toJSON p.${x}}"
                                        (checkNumeric p."${x}"))
                              data))

  (ourCheck "${y} looks numeric" (all (p: ourCheck "Looks numeric ${toJSON p.${y}}"
                                             (looksNumeric p."${y}"))
                                   data))

  (ourCheck "${z} looks numeric" (all (p: ourCheck "Looks numeric ${toJSON p.${z}}"
                                             (looksNumeric p."${z}"))
                                   data))

];

postConditions = result: all id [

  (ourCheck "isAttrs result.series ${toJSON result.series}" (isAttrs result.series))

  (ourCheck "Each series is a list ${toJSON result.series}"
         (all (n: isList result.series."${n}") (attrNames result.series)))

  (ourCheck "Series are (x,y) or (x,y,stddev) ${toJSON result.series}"
         (all (n: any id [
                    (all (row: length row == 2) result.series."${n}")
                    (all (row: length row == 3) result.series."${n}")
                  ])
              (attrNames result.series)))

  (ourCheck "Forcing components of result"
         (all (x: ourCheck "Forcing field ${x}"
                        (isString "${toJSON result.${x}}"))
              (attrNames result)))

  (ourCheck "Force result" (isString "${toJSON result}"))

];

# Wrap our tabulation function in a load of assertions, since there is a lot of
# room for errors which may slip through unnoticed (e.g. one int looks just like
# another).
xVsYForZ = x: y: z: data:
  let result = addErrorContext "Tabulating ${x} vs ${y} for values of ${z}"
                               (xVsYForZReal x y z data);
   in assert ourCheck "Pre-conditions for ${x} vs ${y} per ${z}"
                   (preConditions x y z data);
      assert ourCheck "Post-conditions for ${x} vs ${y} per ${z}"
                   (postConditions result);
      result;

# Performs the actual tabulation of fields
xVsYForZReal = x: y: z: data:
  let # Pull out the required data, and give generic labels (x, y, z)
      points = map (p: {
                     x = p."${x}";
                     y = p."${y}";
                     z = addErrorContext "toString ${toJSON p.${z}}"
                                         (toString p."${z}");
                   }) data;

      # Format points into series, based on their z values
      series = fold ({x, y, z}: out: out // {
                      "${z}" = [(formatPoint x y)] ++ (if out ? "${z}"
                                                        then out."${z}"
                                                        else []);
                    })
                    {}
                    points;

      formatPoint = x: y:
        let xval   = addErrorContext "Rendering ${toJSON x}" (toString x);
            yval   = if isAttrs y
                        then y.mean.estPoint
                        else addErrorContext "Rendering ${toJSON y}"
                                             (toString y);
            stddev = if isAttrs y && y ? stddev
                        then [y.stddev.estPoint]
                        else [];
         in [xval yval] ++ stddev;

   in { inherit x y z series; };

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
           data = dataByClusterCount;
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
           data = dataByClusterCount;
         }

       ]);

in

assert ourCheck "Checking tabulate inputs" (all id [

  (ourCheck "packageNames is list ${toJSON packageNames}"
         (isList packageNames))

  (ourCheck "Package names are strings ${toJSON packageNames}"
         (all isString packageNames))

  (ourCheck "'quick' is a boolean ${toJSON quick}" (isBool quick))

]);

assert ourCheck "Checking tabulate data" (all id [

  (ourCheck "isList dataByClusterCount ${toJSON dataByClusterCount}"
         (isList dataByClusterCount))

  (ourCheck "All dataByClusterCount have required fields"
         (all (f: ourCheck "All dataByClusterCount have ${f}"
                        (all (p: ourCheck "${f} appears in ${toJSON p}"
                                       (p ? "${f}"))
                             dataByClusterCount))
              ["eqCount" "totalTime" "clusterCount"]))

]);

assert ourCheck "Checking tabulate output" (all id [

  (ourCheck "isAttrs tabulated (${typeOf tabulated})" (isAttrs tabulated))

  (ourCheck "tabulated contains sets"
         (all (t: ourCheck "isAttrs ${typeOf tabulated.${t}}"
                        (isAttrs tabulated."${t}"))
              (attrNames tabulated)))

  (ourCheck "Forcing tabulated results"
         (all (n: ourCheck "Forcing ${n}"
                        (isString "${toJSON tabulated.${n}}"))
              (attrNames tabulated)))

]);

tabulated
