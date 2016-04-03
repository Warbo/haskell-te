defs: with defs;

# Run the tests in ./pkgTests with a selection of Haskell package names

let tests        = importDir ./pkgTests;
    hsPkgs       = listToAttrs (map (n: {
                     name  = n;
                     value = processedPackages."${n}" // {
                       runTypes  = testRunTypes."${n}";
                       annotated = testAnnotated."${n}";
                     };
                   }) testPackageNames);
    runTest      = testName: collate (mapAttrs (runTestOnPkg testName) hsPkgs);
    runTestOnPkg = testName: pkgName: pkg:
      let msg =  "Running test '${testName}' with Haskell package '${pkgName}'";
       in trace msg (assertMsg (tests."${testName}" defs pkg) msg);
    collate      = xs: all (n: xs."${n}") (attrNames xs);
 in all runTest (attrNames tests)
