defs: with defs; pkg:
with builtins;

parseJSON (readFile "${pkg.ranTypes}") ? scoperesult
