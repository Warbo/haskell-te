# Import useful stuff
let pkgs = import <nixpkgs> {};
    defs = pkgs // pkgs.lib // builtins // import ./defs-default.nix;
 in with defs;

# Import all *.nix files from ./tests, pass defs to each and assert that they
# return true
let tests   = importDir ./tests;
    runTest = name: let result = tests."${name}" defs;
                     in trace "Running test '${name}'" (assert result; result);
 in all runTest (attrNames tests)
