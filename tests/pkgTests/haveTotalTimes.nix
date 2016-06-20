defs: with defs; pkg:
with builtins;

let slowPkgs    = processPackages { quick = false; };
    check       = times: all (n: isString times."${n}".mean.estPoint)
                             (attrNames times);
    checksQuick = testMsg (check pkg.totalTimes)
                          "Check ${pkg.name} has total quick time";
    checksSlow  = testMsg (check slowPkgs.${pkg.name}.totalTimes)
                          "Check ${pkg.name} has total slow time";
 in checksQuick && checksSlow
