# Import useful stuff
let pkgs = import <nixpkgs> {};
    defs = pkgs // pkgs.lib // builtins // import ./defs-default.nix;
in with defs;

# Import all *.nix files from ./tests, pass defs to each and assert that they
# return true
let tests   = importDir ./tests;
    runTest = name: assertMsg (tests."${name}" defs) "Running test '${name}'";
 in all runTest (attrNames tests)
