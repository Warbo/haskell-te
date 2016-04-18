# Import useful stuff
let pkgs = import ./. {};
 in with pkgs; with builtins; with lib;

# Import all *.nix files from ./tests, pass pkgs to each and assert that they
# return true
let tests       = importDir ../tests;
    runTest     = name: testMsg (tests."${name}" pkgs) "Running test '${name}'";
    testResults = map runTest (attrNames tests);

    # Force testResults, so one failing test doesn't short-circuit the stop the
    # others from being run.
    result      = assert isString "Forcing ${toJSON testResults}";
                  all id testResults;
 in testMsg result "All tests passed"
