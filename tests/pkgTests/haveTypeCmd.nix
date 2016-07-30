defs: with defs; pkg:
with builtins;

testMsg (parseJSON (readFile pkg.ranTypes) ? cmd)
        "'${pkg.name}' has type command"
