defs: with defs; pkg:
with builtins;
with lib;

testMsg (!(parseJSON (readFile (toString pkg.rawClustered.failed))))
        "${pkg.name} clustering didn't fail"
