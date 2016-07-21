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

checkTable = tbl: addErrorContext "Checking table '${toJSON tbl}'"
  (testAll [
    (testMsg (isAttrs tbl.series)
             "Table has a set of series ${toJSON tbl.series}")

    (testMsg (all (n: isList tbl.series."${n}") (attrNames tbl.series))
             "Table rows are lists ${toJSON tbl.series}")

    (testAll (map (n: testAll (map hasValues tbl.series."${n}"))
                              (attrNames tbl.series)))
  ]);

in

testAll (map checkTable [
  eqsVsTimeForClusters
])
