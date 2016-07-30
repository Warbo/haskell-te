defs: with defs; pkg:
with builtins;

testMsg (parseJSON (readFile pkg.ranTypes) ? result)
        "${pkg.name} has ranTypes.result"
