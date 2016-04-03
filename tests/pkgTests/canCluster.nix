defs: with defs;

pkg:

let check    = x: isString x.time.mean.estPoint;
    checkAll = all check;
in assertMsg (checkAll pkg.quickClustered) "Quick" &&
   assertMsg (checkAll pkg.slowClustered)  "Slow"
