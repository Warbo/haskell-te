defs: with defs;
with lib;
with tabulate { clusters     = defaultClusters;
                quick        = true;
                packageNames = [ "list-extras" ]; };
with plotResults;
with builtins;

# Checks all elements of the given set
let

setEq   = xs: ys: all (flip elem xs) ys && all (flip elem ys) xs;

linesEq = s1: s2: testMsg (setEq (splitString "\n" s1)
                                 (splitString "\n" s2))
                          "Lines ${toJSON s1} match lines ${toJSON s2}";
tests = {

mkTblWorks =
  let calc = mkTbl [ { name = "Foo"; key = "foo"; }
                     { name = "Bar"; key = "bar"; }
                     { name = "Baz"; key = "baz"; } ]
                   { x = { foo = "1"; bar = "2"; baz = "3"; };
                     y = { bar = "5"; baz = "6"; foo = "4"; };
                     z = { foo = "7"; baz = "9"; bar = "8"; }; };
      expect = ''
        Foo	Bar	Baz
        1	2	3
        4	5	6
        7	8	9'';
   in testMsg (linesEq calc expect) "mkTbl works";

eqsVsTimeForClustersWorks =
  let tbl = eqsVsTimeForClusters;
   in testMsg (all id [
        (testMsg (isString (renderTable tbl))     "Can render table")
        (testMsg (renderTable tbl != "")          "Rendered table isn't empty")
      ]) "Equations vs time for clusters works";
};

in testMsg (all (n: testMsg tests.${n} "Checking ${n}")
                (attrNames tests))
           "Testing ${toJSON tests}"
