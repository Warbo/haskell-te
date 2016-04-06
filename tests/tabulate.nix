defs: with defs;
with lib;
with tabulate;

# Checks all elements of the given set
let setEq   = xs: ys: all (flip elem xs) ys && all (flip elem ys) xs;
    linesEq = s1: s2: testMsg (setEq (splitString "\n" s1)
                                     (splitString "\n" s2))
                              "Lines:\n${s1}\nMatch lines:\n${s2}";
    tests = {

mkTblWorks =
  let calc = mkTbl [ { name = "Foo"; key = "foo"; }
                     { name = "Bar"; key = "bar"; }
                     { name = "Baz"; key = "baz"; } ]
                   { x = { foo = "1"; bar = "2"; baz = "3"; };
                     y = { bar = "5"; baz = "6"; foo = "4"; };
                     z = { foo = "7"; baz = "9"; bar = "8"; }; };
      expect = ''Foo	Bar	Baz
                 1	2	3
                 4	5	6
                 7	8	9'';
   in linesEq calc expect;

eqsVsTimeForKsWorks =
  let calc = eqsVsTimeForKs ["1" "2" "3"] [
        {}
      ];
      expect = ''t1	k11	k21	k31
                 t2	k12	k22	k32
                 t3	k13	k23	k33'';
  in linesEq calc expect;
};

in all (n: testMsg tests."${n}" "Checking ${n}") (attrNames tests)
