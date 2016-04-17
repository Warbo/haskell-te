defs: with defs; pkg:
with builtins;
with lib;
with tabulate {
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
    (testMsg (isAttrs tbl)
             "Table is a set of series ${toJSON tbl}")

    (testMsg (all (n: isList tbl.${n}) (attrNames tbl))
             "Table rows are lists ${toJSON tbl}")

    (testMsg (all (n: all hasValues tbl.${n}) (attrNames tbl))
             "Table cells contain values ${toJSON tbl}")
  ]);

in

all checkTable [
  eqsVsTimeForClusters
]
