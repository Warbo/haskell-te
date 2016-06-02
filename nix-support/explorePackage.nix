with import ./. {};
with builtins;

pkgDir:

let pkgDef = nixFromCabal (toString pkgDir) null;
    cached = haskellPackages.callPackage pkgDef {};
    pkg    = cached // { inherit currentTime; };
    result = processPackage { quick = true; } pkg.name pkg;
 in if result.failed
       then "FAILED"
       else builtins.attrNames result
