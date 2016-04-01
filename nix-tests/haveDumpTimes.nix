defs: with defs;

let haveMean   = name: result: assertMsg
      (isString result.mean.estPoint)
      "Checking '${name}' result '${toJSON result}' has 'mean.estPoint'";
    haveStdDev = name: result: assertMsg
      (isString result.stddev.estPoint)
      "Checking '${name}' result '${toJSON result}' has 'stddev.estPoint'";
    checkTimes = name: all id [
      (haveMean   name dumpTimesQuick."${name}")
      (haveMean   name dumpTimesSlow."${name}")
      (haveStdDev name dumpTimesSlow."${name}")
    ];
in all checkTimes testPackageNames
