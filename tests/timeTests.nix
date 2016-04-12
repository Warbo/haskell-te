defs: with defs;
with builtins;
with lib;

let

tC = import ../nix-support/timeCalc.nix {
       inherit (defs) assertMsg bc lib parseJSON runScript;

       # To appease timeCalc's signature
       annotateTime = two;
       clusterTimes = {};
       dumpTime     = two;
       exploreTimes = {};
     };

two  = { mean = { estPoint = "2"; }; };
two2 = tC.sumTimes [ two ];
four = tC.sumTimes [ two two ];

in

all id [
  (testMsg (two.mean.estPoint  == "2")
           "sum [2] should equal 2, got ${toJSON two}")

  (testMsg (four.mean.estPoint == "4")
           "sum [2 2] should equal 4, got ${toJSON four}")
]
