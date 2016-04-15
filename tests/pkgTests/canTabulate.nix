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

isValue = x: testMsg (isString x || checkTime x)
                     "isValue ${toJSON x}";

checkTable = tbl: addErrorContext "Checking table '${toJSON tbl}'"
  (with tbl; all id [
    (testMsg (isList matrix)
             "Table body is a list ${toJSON matrix}")

    (testMsg (all isList matrix)
             "Table rows are lists ${toJSON matrix}")

    (testMsg (all (all hasValues) matrix)
             "Table cells contain values ${toJSON matrix}")
  ]);

in

all checkTable [
  eqsVsTimeForClusters
]
