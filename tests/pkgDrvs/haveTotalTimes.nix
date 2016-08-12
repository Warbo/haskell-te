defs: with defs; pkg:
with builtins;
with lib;

let slowPkgs    = processPackages { quick = false; };
    check       = times: mapAttrs (n: t: drvFromScript { inherit t; } ''
                                     touch "$out"
                                     R=$(jq -r '.mean.estPoint | type' < "$t")
                                     [[ "x$R" = "xnumber" ]] && exit 0
                                     [[ "x$R" = "xstring" ]] && exit 0
                                     echo "t: $t , R: $R" 1>&2
                                     exit 1
                                  '')
                                  times;
    checksQuick = check pkg.totalTimes;
    checksSlow  = check slowPkgs."${pkg.name}".totalTimes;
 in { inherit checksQuick checksSlow; }
