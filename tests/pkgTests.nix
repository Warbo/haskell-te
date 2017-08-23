defs: with defs;
with builtins;
with lib;

# Run tests ./pkgTests

let

tests = importDir ./pkgTests;

# Apply the given test to all testPackages
testOnPkgs = _: test:
  mapAttrs (_: pkg: test defs pkg) testPackages;

in mapAttrs testOnPkgs tests
