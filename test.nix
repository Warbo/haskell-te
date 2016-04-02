# Import useful stuff
let pkgs = import <nixpkgs> {};
    defs = pkgs // pkgs.lib // builtins // import ./nix-support {};
 in with defs;

# Import all *.nix files from ./tests, pass defs to each and assert that they
# return true
let tests   = importDir ./nix-tests;
    runTest = name: let msg = "Running test '${name}'";
                     in trace msg (assertMsg (tests."${name}" defs) msg);
 in all runTest (attrNames tests)
