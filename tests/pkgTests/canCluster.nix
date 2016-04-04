defs: with defs;

pkg:

let check    = xs: n: isString xs."${n}".time.mean.estPoint;
    checkAll = xs: all (check xs) (attrNames xs);
in assertMsg (checkAll pkg.quickClustered) "Quick" &&
   assertMsg (checkAll pkg.slowClustered)  "Slow"
