defs: with defs;
with builtins;
with lib;

# Run the tests in tests/testDrvs directly

let

tests = importDir ../tests/testDrvs;

doTest = testName: tst: tst defs;

in mapAttrs doTest tests
