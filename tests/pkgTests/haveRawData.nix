defs: with defs; pkg:
with builtins;

let asts    = downloadAndDump { quick = true; pkgName = pkg.name; };
    rawData = runTypes asts.stdout pkg.name;
 in (readFile "${rawData}") != ""
