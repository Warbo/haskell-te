defs: with defs;

# Run the tests in ./pkgTests with a selection of Haskell package names

let tests        = importDir ./pkgTests;
    runTest      = testName: all (runTestOnPkg testName) testPackageNames;
    runTestOnPkg = testName: hsPkg:
      let msg =  "Running test '${testName}' with Haskell package '${hsPkg}'";
       in trace msg (assertMsg (tests."${testName}" defs hsPkg) msg);
 in all runTest (attrNames tests)
