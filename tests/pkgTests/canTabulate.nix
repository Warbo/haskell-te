defs: with defs; pkg:
with builtins;
with lib;
with tabulate {
  count        = 1;
  clusters     = defaultClusters;
  quick        = false;
  packageNames = [ pkg.name ];
};

# Checking the value types forces them to be evaluated
let

hasValues = x: addErrorContext "hasValues ${toJSON x}"
                 (testAll [(testMsg (isList x) "Got list")
                           (testAll (map isValue x))]);

isValue = x: addErrorContext "isValue ${toJSON x}"
               (testMsg (isInt x || isString x)
                        "isValue ${toJSON x}");

in testAll [
  (testMsg (isAttrs eqsVsTimeForClusters.series)
           "Table has a set of series ${toJSON eqsVsTimeForClusters.series}")

  (testMsg (all (n: isList eqsVsTimeForClusters.series."${n}") (attrNames eqsVsTimeForClusters.series))
           "Table rows are lists ${toJSON eqsVsTimeForClusters.series}")

  (testAll (map (n: testAll (map hasValues eqsVsTimeForClusters.series."${n}"))
                (attrNames eqsVsTimeForClusters.series)))
]
