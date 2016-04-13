defs: with defs;
with builtins;
with lib;

# Run the tests in ./pkgTests with testPackages

let

tests = importDir ./pkgTests;

# Apply the given test to all testPackages
testOnPkgs = testName: test: mapAttrs (run testName test) testPackages;

# Run the given test on the given package
run = testName: test: pkgName: pkg:
        testMsg (test defs pkg) "Testing ${testName} on ${pkgName}";

# All results, with no collation
resultsPerTestPerPkg = mapAttrs testOnPkgs tests;

# Collate results per test: if a test fails for one package, don't keep trying
# it on others
resultsPerTest = mapAttrs (_: results: all id (attrValues results))
                          resultsPerTestPerPkg;

# Strip test names, since they're in our assertion messages anyway
resultList = attrValues resultsPerTest;

in

# Force all test results, to avoid one failing test short-circuiting the rest
assert isString "Forcing ${toJSON resultList}";

all id resultList
