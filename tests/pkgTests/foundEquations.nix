defs: with defs; pkg:
with builtins;
with lib;

let

counts = fold (n: old: old ++ [pkg.equationCounts."${n}"])
              []
              (attrNames pkg.equationCounts);

in testRun "${pkg.name} has non-zero equation count" null
           { inherit counts; } ''
             EMPTY=0
             for X in $counts
             do
               C=$(cat "$X")
               echo -e "Checking '$X', containing '$C'" 1>&2
               O=$(jq -r -n --argjson x "$C" '$x > 0')
               [[ "x$O" = "xtrue" ]] || EMPTY=1
             done
             [[ "$EMPTY" -eq 0 ]] || exit 1
           ''
