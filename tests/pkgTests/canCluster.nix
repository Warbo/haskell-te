defs: with defs;

pkg:

let check    = xs: n: isString xs."${n}".time.mean.estPoint;
    checkAll = xs: all (check xs) (attrNames xs);
in testMsg (checkAll pkg.quickClustered) "Quick" &&
   testMsg (checkAll pkg.slowClustered)  "Slow"
