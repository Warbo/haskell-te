defs: with defs;
with builtins;
with lib;

# Package tests which are safe to import as-is (they won't slow down evaluation)
let tests      = importDir ./pkgDrvs;

    testOnPkgs = _: test:
      mapAttrs (_: pkg: test defs pkg)
               testPackages;
 in mapAttrs testOnPkgs tests
