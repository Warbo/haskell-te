defs: with defs;

# FIXME
let check               = name: result: isString (result.mean.estPoint);
    checksWithTime      = mapAttrs check totalWithTime;
    checksWithCriterion = mapAttrs check totalWithCriterion;
    real = all (pkg: checksWithTime."${pkg}" && checksWithCriterion."${pkg}")
        testPackageNames;
 in true
