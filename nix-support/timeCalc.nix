{ bc, ourCheck, checkStdDev, checkTime, lib, nth, parseJSON, runScript }:
with builtins;
with lib;

rec {

# Assertions

forceVal = x: msg: ourCheck msg (isString "${toJSON x}");

areTimes = ts:
  assert ourCheck "All attributes are times"
               (all (n: assert ourCheck "'${n}' (${toJSON ts.${n}}) is time"
                                     (checkTime ts."${n}");
                        true)
                    (attrNames ts));
  true;

areTimeLists = ts:
  assert ourCheck "All attributes are time lists"
               (all (n: assert ourCheck "'${n}' (${toJSON ts.${n}}) contains times"
                                     (all (x: assert ourCheck "checkTime ${toJSON x}"
                                                           (checkTime x);
                                              true)
                                          ts."${n}");
                        true)
                    (attrNames ts));
  true;

# Arithmetic

floatLessThan = x: y:
  assert isString x;
  assert isString y;
  let result = parseJSON (runScript { buildInputs = [ bc ]; } ''
                 echo 'scale=16; ${x} < ${y}' | bc > "$out"
               '');
   in result == "1";

floatAdd = x: y:
  assert isString x;
  assert isString y;
  parseJSON (runScript { buildInputs = [ bc ]; } ''
    echo 'scale=16; ${x} + ${y}' | bc > "$out"
  '');

addMeans = x: y:
  assert checkTime x;
  assert checkTime y;
  { mean = { estPoint = floatAdd x.mean.estPoint y.mean.estPoint; }; };

addStdDevs = x: y:
  assert ourCheck "stddev is string ${toJSON x}" (isString x);
  assert ourCheck "stddev is string ${toJSON y}" (isString y);
  parseJSON (runScript { buildInputs = [ bc ]; } ''
    echo 'scale=16; sqrt( (${x} * ${x}) + (${y} * ${y}))' | bc > "$out"
  '');

addTimes = x: y:
  assert ourCheck "Given time ${toJSON x}" (x == null || checkTime x);
  assert ourCheck "Given time ${toJSON y}" (y == null || checkTime y);
  let result = if x == null
                  then y
                  else if y == null
                          then x
                          else assert ourCheck "doSum is a time ${toJSON doSum}"
                                            (checkTime doSum);
                               assert ourCheck "doSum stddev OK"
                                            (haveStdDev -> checkStdDev doSum.stddev);
                               doSum;
      doSum = addMeans x y // (if haveStdDev
                                  then { stddev = { estPoint = sumStdDev; }; }
                                  else {});
      haveStdDev = assert ourCheck "Both have stddev ${toJSON [x y]}"
                                (   x ? stddev  ->    y ? stddev);
                   assert ourCheck "Neither have stddev ${toJSON [x y]}"
                                ((! x ? stddev) -> (! y ? stddev));
                   x ? stddev;
      sumStdDev = addStdDevs x.stddev.estPoint y.stddev.estPoint;
   in assert ourCheck "Result is a time ${toJSON result}" (checkTime result);
      result;

sumTimes = fold addTimes null;

# For coarse-grained series, we want to group together many times. To achieve
# this, we group them into "buckets" based on their mean
timeToBucket = t:
  let findBucket = n:
        if floatLessThan t.mean.estPoint (toString n)
           then n
           else findBucket (n * 10);
   in assert ourCheck "Bucketing a time ${toJSON t}" (checkTime t);
      findBucket 1;

# Utilities

indices = l: range 1 (length l);

# Times

pkgTimes = { annotateTime, clusterTimes, dumpTime, exploreTimes }:
  let staticTime = sumTimes [ dumpTime annotateTime ];

      dynamicTimes = mapAttrs (cCount: arr: sumTimes (
                                              [clusterTimes."${cCount}"] ++
                                              exploreTimes."${cCount}"))
                              exploreTimes; # exploreTimes has the structure we want

      totalTimes = mapAttrs (_: t: sumTimes [t staticTime])
                            dynamicTimes;

   in # Check that inputs appear correct
      assert ourCheck " checkTime          dumpTime " ( checkTime          dumpTime );
      assert ourCheck " checkTime      annotateTime " ( checkTime      annotateTime );
      assert ourCheck "areTimes      clusterTimes" (areTimes      clusterTimes);
      assert ourCheck "areTimeLists  exploreTimes" (areTimeLists  exploreTimes);

      # Wrap each output attribute in assertions, so they'll be checked if they're
      # ever used
      {
        dynamicTimes = assert forceVal dynamicTimes "Forcing dynamicTimes";
                       assert ourCheck "areTimes dynamicTimes"
                                    (areTimes dynamicTimes);
                       dynamicTimes;

         staticTime  = assert forceVal  staticTime  "Forcing  staticTime ";
                       assert ourCheck "checkTime staticTime"
                                    (checkTime staticTime);
                       staticTime;

          totalTimes = assert forceVal   totalTimes "Forcing   totalTimes";
                       assert ourCheck "areTimes totalTimes"
                                    (areTimes totalTimes);
                       totalTimes;
      };
}
