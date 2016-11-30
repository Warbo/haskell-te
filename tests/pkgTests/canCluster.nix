defs: with defs; pkg:
with builtins;
with lib;

let v = pkg.rawClustered.results;
 in testMsg (isString v.time.mean.estPoint)
            "${pkg.name} has mean time"
