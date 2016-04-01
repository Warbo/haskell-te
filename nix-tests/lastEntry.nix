defs: with defs;

let result = runScript {} ''
               echo -e 'foo\n-----\nbar\n-----\nbaz' > input
               "${lastEntry}" input > "$out"
             '';
    expected = "baz\n";
 in assertMsg (result == expected) "Checking if '${result}' == '${expected}'"
