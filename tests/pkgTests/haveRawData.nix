defs: with defs; pkg:
with builtins;

let rawData = runTypes pkg.rawDump.stdout pkg {};
 in testRun "${pkg.name} has raw data" null { inherit rawData; }
            ''[[ -n "$rawData" ]] || exit 1''
