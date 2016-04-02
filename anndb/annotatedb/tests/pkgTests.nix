defs: with defs;

# Run the tests in ./pkgTests with a selection of Haskell package names

let hsPkgs       = [ "list-extras" "xmonad" ];
    tests        = importDir ./pkgTests;
    runTest      = testName: all (runTestOnPkg testName) hsPkgs;
    runTestOnPkg = testName: hsPkg:
      assertMsg (tests."${testName}" defs hsPkg)
                "Running test '${testName}' with Haskell package '${hsPkg}'";
 in all runTest (attrNames tests)
