{ bc, check, checkStdDev, checkTime, lib, nth, parseJSON, runScript }:
with builtins;
with lib;

rec {

# Assertions

forceVal = x: msg: check msg (isString "${toJSON x}");

areTimes = ts:
  assert check "All attributes are times"
               (all (n: assert check "'${n}' (${toJSON ts.${n}}) is time"
                                     (checkTime ts.${n});
                        true)
                    (attrNames ts));
  true;

areTimeLists = ts:
  assert check "All attributes are time lists"
               (all (n: assert check "'${n}' (${toJSON ts.${n}}) contains times"
                                     (all (x: assert check "checkTime ${toJSON x}"
                                                           (checkTime x);
                                              true)
                                          ts.${n});
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
  assert check "stddev is string ${toJSON x}" (isString x);
  assert check "stddev is string ${toJSON y}" (isString y);
  parseJSON (runScript { buildInputs = [ bc ]; } ''
    echo 'scale=16; sqrt( (${x} * ${x}) + (${y} * ${y}))' | bc > "$out"
  '');

addTimes = x: y:
  assert check "Given time ${toJSON x}" (x == null || checkTime x);
  assert check "Given time ${toJSON y}" (y == null || checkTime y);
  let result = if x == null
                  then y
                  else if y == null
                          then x
                          else assert check "doSum is a time ${toJSON doSum}"
                                            (checkTime doSum);
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
   in assert check "Result is a time ${toJSON result}" (checkTime result);
      result;

sumTimes = fold addTimes null;

# For coarse-grained series, we want to group together many times. To achieve
# this, we group them into "buckets" based on their mean
timeToBucket = t:
  let findBucket = n:
        if floatLessThan t.mean.estPoint (toString n)
           then n
           else findBucket (n * 10);
   in assert check "Bucketing a time ${toJSON t}" (checkTime t);
      findBucket 1;

# Utilities

indices = l: range 1 (length l);

# Times

pkgTimes = { annotateTime, clusterTimes, dumpTime, exploreTimes }:
  let staticTime = sumTimes [ dumpTime annotateTime ];

      dynamicTimes = mapAttrs (cCount: arr: map (n: sumTimes [
                                                  clusterTimes.${cCount}
                                                  (nth n exploreTimes.${cCount})
                                                ])
                                                (indices exploreTimes.${cCount}))
                              exploreTimes; # exploreTimes has the structure we want

      totalTimes = mapAttrs (c: map (t: sumTimes [t staticTime]))
                            dynamicTimes;

   # Force inputs, to expose any latent errors
   in assert forceVal     dumpTime  "Forcing     dumpTime ";
      assert forceVal annotateTime  "Forcing annotateTime ";
      assert forceVal  clusterTimes "Forcing  clusterTimes";
      assert forceVal  exploreTimes "Forcing  exploreTimes";

      # Check that inputs appear correct
      assert check " checkTime          dumpTime " ( checkTime          dumpTime );
      assert check " checkTime      annotateTime " ( checkTime      annotateTime );
      assert check "areTimes      clusterTimes" (areTimes      clusterTimes);
      assert check "areTimeLists  exploreTimes" (areTimeLists  exploreTimes);

      # Wrap each output attribute in assertions, so they'll be checked if they're
      # ever used
      {
        dynamicTimes = assert forceVal dynamicTimes "Forcing dynamicTimes";
                       assert check "areTimeLists dynamicTimes"
                                    (areTimeLists dynamicTimes);
                       dynamicTimes;

         staticTime  = assert forceVal  staticTime  "Forcing  staticTime ";
                       assert check "checkTime staticTime"
                                    (checkTime staticTime);
                       staticTime;

          totalTimes = assert forceVal   totalTimes "Forcing   totalTimes";
                       assert check "areTimeLists totalTimes"
                                    (areTimeLists totalTimes);
                       totalTimes;
      };
}
