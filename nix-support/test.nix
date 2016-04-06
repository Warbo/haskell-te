# Import useful stuff
let pkgs = import <nixpkgs> {};
    defs = pkgs // pkgs.lib // builtins // import ./. {};
 in with defs;

# Import all *.nix files from ./tests, pass defs to each and assert that they
# return true
let tests   = importDir ../tests;
    runTest = name: testMsg (tests."${name}" defs) "Running test '${name}'";
    result  = all runTest (attrNames tests);
 in trace (if result then "All tests passed"  else "Tests failed")
          (assert result; result)
