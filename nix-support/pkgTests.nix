defs: with defs;
with builtins;
with lib;

# Run the tests in tests/pkgTests with testPackages

let

tests = importDir ../tests/pkgTests;

# Apply the given test to all testPackages
testOnPkgs = testName: _:
  mapAttrs (pkgName: _:
             runTestInDrv
               "tests/pkgTests/${testName}.nix"
               [ ''((import ./nix-support {}).testPackages."${pkgName}")'' ])
           testPackages;

in mapAttrs testOnPkgs tests
