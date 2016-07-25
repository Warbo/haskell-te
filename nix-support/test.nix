# Import useful stuff
let pkgs = import ./. {};
 in with pkgs; with builtins; with lib;

# Import all *.nix files from ./tests, pass pkgs to each and assert that they
# return true
let tests       = import ./tests.nix { inherit pkgs; };
    testResults = mapAttrs (n: t: dbug "Running test '${n}'" t)
                           tests;

    result      = attrValues testResults;
 in testWrap result "All tests passed"
