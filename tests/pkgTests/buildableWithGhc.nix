defs: with defs; pkg:
with builtins;

testDbg (!(parseJSON (readFile (toString pkg.build.failed)))) "Trying to build" { inherit (pkg.build) failed; }
