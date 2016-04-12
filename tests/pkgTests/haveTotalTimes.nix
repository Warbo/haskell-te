defs: with defs; pkg:
with builtins;

let slowPkgs    = defaultPackages { quick = false; };
    check       = times: all (n: all (x: isString x.mean.estPoint)
                                     times."${n}")
                             (attrNames times);
    checksQuick = testMsg (check pkg.totalTimes)
                          "Check ${pkg.name} has total quick time";
    checksSlow  = testMsg (check slowPkgs.${pkg.name}.totalTimes)
                          "Check ${pkg.name} has total slow time";
 in checksQuick && checksSlow
