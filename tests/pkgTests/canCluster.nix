defs: with defs; pkg:
with builtins;
with lib;

let check    = p: n: v: testMsg (isString v.time.mean.estPoint)
                                "${p}.${n} has mean time";
    checkAll = p: v: mapAttrs (check p) v;
    slow     = processPackages { quick = false; };
    slowPkg  = slow."${pkg.name}";
in mapAttrs checkAll {
  quick =     pkg.rawClustered.results;
  slow  = slowPkg.rawClustered.results;
}
