defs: with defs;

# Run the tests in ./pkgTests with a selection of Haskell package names

let hsPkgs       = [ "list-extras" "xmonad" ];
    tests        = importDir ./pkgTests;
    runTest      = testName: all (runTestOnPkg testName) hsPkgs;
    runTestOnPkg = testName: hsPkg:
      let result = tests."${testName}" defs hsPkg;
       in trace "Running test '${testName}' with Haskell package 'hsPkg'"
                (assert result; result);
 in all runTest (attrNames tests)
