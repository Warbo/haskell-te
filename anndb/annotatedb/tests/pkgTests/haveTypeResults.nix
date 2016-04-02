defs: with defs;

pkgName:

let rawData = runTypes (dumpedPackages."${pkgName}") pkgName;
    result  = addErrorContext "Parsing contents of '${rawData}'"
                              (fromJSON (readFile "${rawData}"));
 in result ? result
