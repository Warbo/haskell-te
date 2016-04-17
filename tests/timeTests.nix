defs: with defs;
with builtins;
with lib;

let

two  = { mean = { estPoint = "2"; }; };
two2 = timeCalc.sumTimes [ two ];
four = timeCalc.sumTimes [ two two ];

in

all id [
  (testMsg (two.mean.estPoint  == "2")
           "sum [2] should equal 2, got ${toJSON two}")

  (testMsg (four.mean.estPoint == "4")
           "sum [2 2] should equal 4, got ${toJSON four}")

  (testMsg (timeCalc.floatLessThan "1.2345678" "2.3456789") "1.x < 2.x")

  (testMsg (! timeCalc.floatLessThan "1.2345678" "0.1234567") "0.x < 1.x")

  (testMsg (! timeCalc.floatLessThan "1.2345678" "1.2345678") "! (x < x)")
]
