{ bc, ourCheck, checkStdDev, checkTime, drvFromScript, lib, nth, parseJSON,
  runScript }:
with builtins;
with lib;

rec {

sumTimeDrvs = ts: if ts == []
                     then null
                     else if length ts == 1
                             then head ts
                             else addMaybeTimes (head ts)
                                                (sumTimeDrvs (tail ts));

addMaybeTimes = x: y: if x == null
                         then y
                         else if y == null
                                 then x
                                 else addTimeDrvs x y;

addTimeDrvs = x: y: drvFromScript { inherit x y; } ''
                      echo -e "x: $x\ny: $y" 1>&2

                      XM=$(jq -r   '.mean.estPoint' < "$x")
                      YM=$(jq -r   '.mean.estPoint' < "$y")
                      XS=$(jq -r '.stddev.estPoint' < "$x")
                      YS=$(jq -r '.stddev.estPoint' < "$y")

                      echo -e "XM: $XM\nYM: $YM\nXS: $XS\nYS: $YS" 1>&2

                        MEAN='{"mean"  :{"estPoint": ($xm+$ym)}}'
                      STDDEV='{"stddev":{"estPoint": ($xs+$ys)}}'
                       CHECK='$xs == null'

                      jq -n --argjson xm "$XM" \
                            --argjson ym "$YM" \
                            --argjson xs "$XS" \
                            --argjson ys "$YS" \
                            "$MEAN + if $CHECK then {} else $STDDEV end" > "$out"
                    '';

pkgTimes = { annotateTime, clusterTimes, dumpTime, exploreTimes }:
  let staticTime = addTimeDrvs dumpTime annotateTime;

      dynamicTimes = mapAttrs (cCount: arr: sumTimeDrvs (
                                              [clusterTimes."${cCount}"] ++
                                               exploreTimes."${cCount}"))
                              exploreTimes; # exploreTimes has the structure we want

      totalTimes = mapAttrs (_: t: sumTimeDrvs [t staticTime])
                            dynamicTimes;

   in trace "FIXME: Check times in derivation" {
        inherit dynamicTimes staticTime totalTimes;
      };
}
