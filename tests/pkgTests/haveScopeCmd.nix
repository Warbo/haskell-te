defs: with defs; pkg:
with builtins;

testMsg (parseJSON (readFile pkg.ranTypes) ? scopecmd)
        "${pkg.name} has scope command"
