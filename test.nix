# Import useful stuff
let pkgs = import <nixpkgs> {};
    defs = pkgs // pkgs.lib // builtins // import ./nix-support {};
 in with defs;

# Import all *.nix files from ./tests, pass defs to each and assert that they
# return true
let tests   = importDir ./nix-tests;
    runTest = name: assertMsg (tests."${name}" defs) "Running test '${name}'";
 in all runTest (attrNames tests)
