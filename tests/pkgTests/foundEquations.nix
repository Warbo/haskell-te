defs: with defs; pkg:
with builtins;
with lib;

let

counts = fold (n: old: old ++ [pkg.equationCounts."${n}"])
              []
              (attrNames pkg.equationCounts);

info = pkg // { pkg = "Elided"; };

test = testDbg
         (any (x: x > 0) counts)
         "${pkg.name} has non-zero equation count ${toJSON pkg.equationCounts}"
         "Debug: ${toJSON info}";

in test
