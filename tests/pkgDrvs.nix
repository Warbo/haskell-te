defs: with defs;
with builtins;
with lib;

let tests      = importDir ./pkgTests;

    testOnPkgs = _: test:
      mapAttrs (_: pkg: test defs pkg)
               testPackages;
 in mapAttrs testOnPkgs tests
