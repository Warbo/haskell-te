{ bc, lib }:
with builtins;
with lib;

let  floatAdd = x: y:
       assert isString x;
       assert isString y;
       parseJSON (runScript { buildInputs = [ bc ]; } ''
         echo 'scale=16; ${x} + ${y}' | bc > "$out"
       '');
     addTimes = x: y: if y == null then x else {
                         mean = {
                           estPoint = floatAdd x.mean.estPoint
                                               y.mean.estPoint;
                         };
                       };
     addCriterion = x: y: trace "FIXME: Handle standard deviation"
                                (if y == null then x else floatAdd x y);
in rec {
  sumWithTime      = fold addTimes     null;
  sumWithCriterion = fold addCriterion null;
}
