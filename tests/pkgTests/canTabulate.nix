defs: with defs; pkg:
with builtins;
with lib;
with tabulate { clusters = defaultClusters; quick = false; };

# Checking the value types forces them to be evaluated
let check = tbl: addErrorContext "Checking '${toJSON tbl}'"
      (with tbl; all id [
        (testMsg (isList matrix)             "Table body is a list")
        (testMsg (all isList matrix)         "Table rows are lists")
        (testMsg (all (all isString) matrix) "Table cells contain strings")
      ]);
 in all check [
      (eqsVsTimeForClusters pkg.sizeDataPoints)
    ]
