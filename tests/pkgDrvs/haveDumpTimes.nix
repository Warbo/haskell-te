defs: with defs; pkg:
with builtins;
with lib;

let haveMean   = result: testRun
      "Checking '${pkg.name}' result has 'mean.estPoint'"
      null
      { inherit result; }
      ''
        T=$(jq -r '.mean.estPoint | type' < "$result")
        echo "Type: $T" 1>&2
        [[ "x$T" = "xstring" ]] && exit 0
        [[ "x$T" = "xnumber" ]] && exit 0
        exit 1
      '';

    haveStdDev = result: testRun
      "Checking '${pkg.name}' result has 'stddev.estPoint'"
      null
      { inherit result; }
      ''
        T=$(jq -r '.stddev.estPoint | type' < "$result")
        echo "Type: $T" 1>&2
        [[ "x$T" = "xstring" ]] && exit 0
        [[ "x$T" = "xnumber" ]] && exit 0
        exit 1
      '';
    slow    = processPackages { quick = false; };
    slowPkg = slow."${pkg.name}";
 in {
   quickMean  = haveMean   pkg.rawDump.time;
   slowMean   = haveMean   slowPkg.rawDump.time;
   slowStdDev = haveStdDev slowPkg.rawDump.time;
 }
