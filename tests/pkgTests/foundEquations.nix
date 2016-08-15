defs: with defs; pkg:
with builtins;
with lib;

let

counts = fold (n: old: old ++ [pkg.equationCounts."${n}"])
              []
              (attrNames pkg.equationCounts);

in testRun "${pkg.name} has non-zero equation count" null
           { inherit counts; } ''
             for X in $counts
             do
               O=$(jq -r -n --argjson x "$X" '$x > 0')
               [[ "x$O" = "xtrue" ]] || exit 1
             done
           '';
