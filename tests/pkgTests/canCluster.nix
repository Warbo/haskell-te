defs: with defs; pkg:
with builtins;

let check    = xs: n: isString xs."${n}".time.mean.estPoint;
    checkAll = xs: all (check xs) (attrNames xs);
    slow     = defaultPackages { quick = false; };
    slowPkg  = slow."${pkg.name}";
in testMsg (checkAll pkg.rawClustered)     "Quick" &&
   testMsg (checkAll slowPkg.rawClustered) "Slow"
