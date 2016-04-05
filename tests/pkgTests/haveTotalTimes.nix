defs: with defs; pkg:

let check               = times: all (n: isString (times."${n}".mean.estPoint))
                                     (attrNames times);
    checksWithTime      = assertMsg (check pkg.totalWithTime)
                                    "Check ${pkg.name} has total quick time";
    checksWithCriterion = assertMsg (check pkg.totalWithCriterion)
                                    "Check ${pkg.name} has total slow time";
 in checksWithTime && checksWithCriterion
