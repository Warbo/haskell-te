defs: with defs;

pkgName:

let rawData = runTypes (downloadAndDump pkgName) pkgName;
 in (readFile "${rawData}") != ""
