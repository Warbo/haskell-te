defs: with defs; pkg:
with builtins;
with lib;

all id [

(testMsg (pkg ? sizeDataPoints) "Have sizeDataPoints")

(testMsg (isList pkg.sizeDataPoints) "sizeDataPoints is a list")

(testMsg (all isAttrs pkg.sizeDataPoints) "Data points are sets")

(all id (map (f: (testMsg (all (p: p ? "${f}") pkg.sizeDataPoints)
                          "Data points have field '${f}'"))
             ["eqCount" "size" "withTime" "withCriterion" "clusterCount"]))

]
