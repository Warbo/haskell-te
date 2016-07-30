defs: with defs; pkg:
with builtins;

let asts    = downloadAndDump { quick = true; pkgName = pkg.name; };
    rawData = runTypes asts.stdout pkg {};
 in testRun "${pkg.name} has raw data" null { inherit rawData; }
            ''[[ -n "${rawData}" ]] || exit 1''
