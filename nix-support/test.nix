# Import useful stuff
let pkgs = import <nixpkgs> {};
 in with pkgs; with builtins;

# Import all *.nix files from ./tests, pass pkgs to each and assert that they
# return true
let tests   = importDir ../tests;
    runTest = name: testMsg (tests."${name}" pkgs) "Running test '${name}'";
    result  = all runTest (attrNames tests);
 in testMsg result "All tests passed"
