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

hasValues = x: testMsg (isList x && all isValue x) "${toJSON x} hasValues";

isValue = x: testMsg (isInt x || isString x)
                     "isValue ${toJSON x}";

checkTable = tbl: addErrorContext "Checking table '${toJSON tbl}'"
  (all id [
    (testMsg (isAttrs tbl.series)
             "Table has a set of series ${toJSON tbl.series}")

    (testMsg (all (n: isList tbl.series.${n}) (attrNames tbl.series))
             "Table rows are lists ${toJSON tbl.series}")

    (testMsg (all (n: all hasValues tbl.series.${n}) (attrNames tbl.series))
             "Table cells contain values ${toJSON tbl.series}")
  ]);

in

all checkTable [
  eqsVsTimeForClusters
]
