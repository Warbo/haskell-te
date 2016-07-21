defs: with defs; pkg:
with builtins;

let check    = xs: n: isString xs."${n}".time.mean.estPoint;
    checkAll = xs: all (check xs) (attrNames xs);
    slow     = processPackages { quick = false; };
    slowPkg  = slow."${pkg.name}";
in testAll [(testMsg (checkAll pkg.rawClustered.results)     "Quick")
            (testMsg (checkAll slowPkg.rawClustered.results) "Slow")]
