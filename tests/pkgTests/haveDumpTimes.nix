defs: with defs; pkg:

let haveMean   = result: assertMsg
      (isString result.mean.estPoint)
      "Checking '${pkg.name}' result '${toJSON result}' has 'mean.estPoint'";
    haveStdDev = result: assertMsg
      (isString result.stddev.estPoint)
      "Checking '${pkg.name}' result '${toJSON result}' has 'stddev.estPoint'";
in  all id [
      (haveMean   pkg.quickDump.time)
      (haveMean   pkg.slowDump.time)
      (haveStdDev pkg.slowDump.time)
    ]
