defs: with defs;
with builtins;
with lib;

# Run tests ./pkgTests, deferring their evaluation to avoid slowdowns

let

tests = importDir ./pkgTests;

# Apply the given test to all testPackages
testOnPkgs = testName: _:
  mapAttrs (pkgName: _:
             runTestInDrv
               "tests/pkgTests/${testName}.nix"
               [ ''((import ./nix-support {}).testPackages."${pkgName}")'' ])
           testPackages;

in mapAttrs testOnPkgs tests
