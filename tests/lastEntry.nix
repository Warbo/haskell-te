defs: with defs;

let result = runScript {} ''
               echo -e 'foo\n-----\nbar\n-----\nbaz' > input
               "${lastEntry}" input > "$out"
             '';
    expected = "baz\n";
 in testMsg (result == expected) "Checking if '${toJSON result}' == '${toJSON expected}'"
