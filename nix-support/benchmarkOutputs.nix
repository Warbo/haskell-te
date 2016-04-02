{ dumpPackage, extractTarball, haskellPackages, lib }:
with lib;

let addTimes         = x: y: {
                         mean = {
                           estPoint = x.mean.estPoint + y.mean.estPoint;
                         };
                       };
    addCriterion     = x: y: x + y; # FIXME
    sumWithTime      = fold addTimes { mean = { estPoint = 0; }; };
    sumWithCriterion = fold addCriterion 0;
    processPkg       = name: pkg: rec {
      inherit name pkg;
      src       = extractTarball pkg.src;
      quickDump = dumpPackage { quick = true;  inherit src; };
      slowDump  = dumpPackage { quick = false; inherit src; };
      dump      = quickDump.stdout; # Stick to the quick output, arbitrarily
    };
 in mapAttrs processPkg haskellPackages
