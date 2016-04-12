{ bc, check, lib, parseJSON, runScript }:
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
  check "All attributes are times"
        (all (n: check "'${n}' (${toJSON ts.${n}}) is time"
                       (isTime ts.${n}))
             (attrNames ts));

areTimeLists = ts:
  check "All attributes are time lists"
        (all (n: check "'${n}' (${toJSON ts.${n}}) contains times"
                       (all (x: check "isTime '${toJSON x}'"
                                      (isTime x))
                            ts.${n}))
             (attrNames ts));

checkStdDev = sd:
  assert check "isAttrs stddev '${toJSON sd}'" (isAttrs sd);
  assert check "Stddev '${toJSON sd}' has estPoint" (sd ? estPoint);
  check "Stddev estPoint '${toJSON sd.estPoint}'" (isString st.estPoint);

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
  assert isString x;
  assert isString y;
  parseJSON (runScript { buildInputs = [ bc ]; } ''
    echo 'scale=16; sqrt( ($x} * ${x}) + (${y} * ${y}))' | bc
  '');

addTimes = x: y:
  assert x == null || isTime x;
  assert y == null || isTime y;
  let result = if x == null
                  then y
                  else if y == null
                          then x
                          else doSum;
      doSum = addMeans x y // (if haveStdDev
                                  then { stddev = sumStdDev; }
                                  else {});
      haveStdDev = assert    x ? stddev  ->    y ? stddev;
                   assert (! x ? stddev) -> (! y ? stddev);
                   x ? stddev;
      sumStdDev = addStdDevs x.stddev y.stddev;
   in assert isTime result;
      assert haveStdDev -> checkStdDev result.stddev;
      result;

sumTimes = fold addTimes null;

# Utilities

nth = n: lst:
  assert check "Given integer '${toJSON n}'" (isInt  n);
  assert check "Expecting list, given '${typeOf lst}'" (isList lst);
  assert check "Index '${toJSON n}' in bounds '${toJSON (length lst)}'"
               (n <= length lst);
  if n == 1
     then head lst
     else nth (n - 1) (tail lst);

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
