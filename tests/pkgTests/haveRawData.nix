defs: with defs;

pkg:

let rawData = runTypes (downloadAndDump pkg.name) pkg.name;
 in (readFile "${rawData}") != ""
