defs: with defs; pkg:
with builtins;
with lib;

let haveMean   = result: testMsg
      (isString result.mean.estPoint)
      "Checking '${pkg.name}' result '${toJSON result}' has 'mean.estPoint'";
    haveStdDev = result: testMsg
      (isString result.stddev.estPoint)
      "Checking '${pkg.name}' result '${toJSON result}' has 'stddev.estPoint'";
    slow    = processPackages { quick = false; };
    slowPkg = slow."${pkg.name}";
 in testAll [
      (haveMean   pkg.rawDump.time)
      (haveMean   slowPkg.rawDump.time)
      (haveStdDev slowPkg.rawDump.time)
    ]
