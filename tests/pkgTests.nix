defs: with defs;

# Run the tests in ./pkgTests with testPackages

let tests        = importDir ./pkgTests;
    runTest      = testName: collate (mapAttrs (runTestOnPkg testName)
                                               testPackages);
    runTestOnPkg = testName: pkgName: pkg:
      testMsg (tests."${testName}" defs pkg)
              "Running test '${testName}' with Haskell package '${pkgName}'";
    collate      = xs: all (n: xs."${n}") (attrNames xs);
 in all runTest (attrNames tests)
