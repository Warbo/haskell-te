defs: with defs;

# Run the tests in ./pkgTests with testPackages

let tests        = importDir ./pkgTests;
    runTest      = testName: collate (mapAttrs (runTestOnPkg testName)
                                               testPackages);
    runTestOnPkg = testName: pkgName: pkg:
      let msg =  "Running test '${testName}' with Haskell package '${pkgName}'";
       in trace msg (assertMsg (tests."${testName}" defs pkg) msg);
    collate      = xs: all (n: xs."${n}") (attrNames xs);
 in all runTest (attrNames tests)
