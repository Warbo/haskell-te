defs: with defs; pkg:
with builtins;
with lib;

testWrap [

(testMsg (pkg ? sizeDataPoints) "Have sizeDataPoints")

(testMsg (isList pkg.sizeDataPoints) "sizeDataPoints is a list")

(testMsg (all isAttrs pkg.sizeDataPoints) "Data points are sets")

(testWrap (map (f: (testMsg (all (p: p ? "${f}") pkg.sizeDataPoints)
                            "Data points have field '${f}'"))
             ["eqCount" "size" "totalTime" "clusterCount"])
          "Data points have all fields")

] "Size datapoints found for${pkg.name}"
