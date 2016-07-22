defs: with defs;
with builtins;

let result = runScript {} ''
               echo -e 'foo\n-----\nbar\n-----\nbaz' > input
               "${lastEntry}" input > "$out"
             '';
    expected = "baz\n";
 in testMsg (result == expected)
            "Checking equality ${toJSON { inherit result expected; }}"
