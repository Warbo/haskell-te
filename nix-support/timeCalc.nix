{ bc, check, lib, nth, parseJSON, runScript }:
{ annotateTime, clusterTimes, dumpTime, exploreTimes }:
with builtins;
with lib;

let

# Assertions

forceVal = x: msg: check msg (isString "${toJSON x}");

isTime = t:
  assert check "isAttrs '${toJSON t}'"           (isAttrs t);
  assert check "${toJSON t} has mean"            (t ? mean);
  assert check "isAttrs '${toJSON t.mean}'"      (isAttrs t.mean);
  assert check "'${toJSON t.mean}' has estPoint" (t.mean ? estPoint);
  t ? stddev -> check "Checking stddev" (checkStdDev t.stddev);

areTimes = ts:
  assert check "All attributes are times"
               (all (n: assert check "'${n}' (${toJSON ts.${n}}) is time"
                                     (isTime ts.${n});
                        true)
                    (attrNames ts));
  true;

areTimeLists = ts:
  assert check "All attributes are time lists"
               (all (n: assert check "'${n}' (${toJSON ts.${n}}) contains times"
                                     (all (x: assert check "isTime ${toJSON x}"
                                                           (isTime x);
                                              true)
                                          ts.${n});
                        true)
                    (attrNames ts));
  true;

checkStdDev = sd:
  assert check "isAttrs stddev '${toJSON sd}'" (isAttrs sd);
  assert check "Stddev '${toJSON sd}' has estPoint" (sd ? estPoint);
  assert check "Stddev estPoint '${toJSON sd.estPoint}'" (isString sd.estPoint);
  true;

# Arithmetic

floatAdd = x: y:
  assert isString x;
  assert isString y;
  parseJSON (runScript { buildInputs = [ bc ]; } ''
    echo 'scale=16; ${x} + ${y}' | bc > "$out"
  '');

addMeans = x: y:
  assert isTime x;
  assert isTime y;
  { mean = { estPoint = floatAdd x.mean.estPoint y.mean.estPoint; }; };

addStdDevs = x: y:
  assert check "stddev is string ${toJSON x}" (isString x);
  assert check "stddev is string ${toJSON y}" (isString y);
  parseJSON (runScript { buildInputs = [ bc ]; } ''
    echo 'scale=16; sqrt( (${x} * ${x}) + (${y} * ${y}))' | bc > "$out"
  '');

addTimes = x: y:
  assert check "Given time ${toJSON x}" (x == null || isTime x);
  assert check "Given time ${toJSON y}" (y == null || isTime y);
  let result = if x == null
                  then y
                  else if y == null
                          then x
                          else assert check "doSum is a time ${toJSON doSum}"
                                            (isTime doSum);
                               assert check "doSum stddev OK"
                                            (haveStdDev -> checkStdDev doSum.stddev);
                               doSum;
      doSum = addMeans x y // (if haveStdDev
                                  then { stddev = { estPoint = sumStdDev; }; }
                                  else {});
      haveStdDev = assert check "Both have stddev ${toJSON [x y]}"
                                (   x ? stddev  ->    y ? stddev);
                   assert check "Neither have stddev ${toJSON [x y]}"
                                ((! x ? stddev) -> (! y ? stddev));
                   x ? stddev;
      sumStdDev = addStdDevs x.stddev.estPoint y.stddev.estPoint;
   in assert check "Result is a time ${toJSON result}" (isTime result);
      result;

sumTimes = fold addTimes null;

# Utilities

indices = l: range 1 (length l);

# Times

staticTime = sumTimes [ dumpTime annotateTime ];

dynamicTimes = mapAttrs (cCount: arr: map (n: sumTimes [
                                            clusterTimes.${cCount}
                                            (nth n exploreTimes.${cCount})
                                          ])
                                          (indices exploreTimes.${cCount}))
                        exploreTimes; # exploreTimes has the structure we want

totalTimes = mapAttrs (c: map (t: sumTimes [t staticTime]))
                      dynamicTimes;

in

# Force inputs, to expose any latent errors
assert forceVal     dumpTime  "Forcing     dumpTime ";
assert forceVal annotateTime  "Forcing annotateTime ";
assert forceVal  clusterTimes "Forcing  clusterTimes";
assert forceVal  exploreTimes "Forcing  exploreTimes";

# Check that inputs appear correct
assert check " isTime          dumpTime " ( isTime          dumpTime );
assert check " isTime      annotateTime " ( isTime      annotateTime );
assert check "areTimes      clusterTimes" (areTimes      clusterTimes);
assert check "areTimeLists  exploreTimes" (areTimeLists  exploreTimes);

# Wrap each output attribute in assertions, so they'll be checked if they're
# ever used
{
  inherit sumTimes; # Expose for testing

  dynamicTimes = assert forceVal dynamicTimes "Forcing dynamicTimes";
                 assert check "areTimeLists dynamicTimes"
                              (areTimeLists dynamicTimes);
                 dynamicTimes;

   staticTime  = assert forceVal  staticTime  "Forcing  staticTime ";
                 assert check "isTime staticTime"
                              (isTime staticTime);
                 staticTime;

    totalTimes = assert forceVal   totalTimes "Forcing   totalTimes";
                 assert check "areTimeLists totalTimes"
                              (areTimeLists totalTimes);
                 totalTimes;
}
