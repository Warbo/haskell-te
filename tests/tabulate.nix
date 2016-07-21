defs: with defs;
with lib;
with tabulate { clusters     = defaultClusters;
                count        = 1;
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
tests = [

  (let calc = mkTbl [ { name = "Foo"; key = "foo"; }
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
    in testWrap [(linesEq calc expect)] "mkTbl works")

  (let rendered = mapAttrs (_: renderTable "x" "y") eqsVsTimeForClusters.series;
       doTest   = series:
         let rows = rendered."${series}";
          in testWrap [
               (testMsg (isString rows)
                        "Can render table ${toJSON rows}")

               (testMsg (rows != "")
                        "Rendered table isn't empty ${toJSON rows}")
             ] "Equations vs Time for clusters works";
    in testWrap (map doTest (attrNames rendered))
                "Equations vs time for clusters works")
];

in testWrap tests "Testing ${toJSON tests}"
