defs: with defs; pkg:

let check               = result: isString (result.mean.estPoint);
    checksWithTime      = assertMsg (check pkg.totalWithTime)
                                    "Check ${pkg.name} has total quick time";
    checksWithCriterion = assertMsg (check pkg.totalWithCriterion)
                                    "Check ${pkg.name} has total slow time";
 in checksWithTime && checksWithCriterion
