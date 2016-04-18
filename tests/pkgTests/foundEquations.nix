defs: with defs; pkg:
with builtins;
with lib;

let

counts = fold (n: old: old ++ pkg.equationCounts.${n})
              []
              (attrNames pkg.equationCounts);

info = pkg // { pkg = "Elided"; };

debug = x: if x then x
                else trace "Debug: ${toJSON info}" x;

test = testMsg
         (any (x: x > 0) counts)
         "${pkg.name} has non-zero equation count ${toJSON pkg.equationCounts}";

in debug test
