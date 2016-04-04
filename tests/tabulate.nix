defs: with defs;
with lib;

let calc = mkTbl [ { name = "Foo"; key = "foo"; }
                   { name = "Bar"; key = "bar"; }
                   { name = "Baz"; key = "baz"; } ]
                 { x = { foo = "1"; bar = "2"; baz = "3"; };
                   y = { bar = "5"; baz = "6"; foo = "4"; };
                   z = { foo = "7"; baz = "9"; bar = "8"; }; };
    expect = [ "Foo\tBar\tBaz"
               "1\t2\t3"
               "4\t5\t6"
               "7\t8\t9" ];
    lines = splitString "\n" calc;
 in assertMsg (all (flip elem expect) lines)  "All lines expected" &&
    assertMsg (all (flip elem lines)  expect) "All expected lines"
