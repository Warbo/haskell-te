defs: with defs; pkg:
with builtins;

testMsg (parseJSON (readFile "${pkg.ranTypes}") ? scoperesult)
        "${pkg.name} has scoperesult"
