defs: with defs; pkg:
with builtins;
with lib;

let

counts = fold (n: old: old ++ [pkg.equationCounts."${n}"])
              []
              (attrNames pkg.equationCounts);

in testRun "${pkg.name} has non-zero equation count" null
           { inherit counts; } ''
             NONEMPTY=0
             for X in $counts
             do
               C=$(cat "$X")
               echo -e "Checking '$X', containing '$C'" 1>&2
               [[ "$C" -eq 0 ]] || NONEMPTY=1
             done
             [[ "$NONEMPTY" -eq 1 ]] || exit 1
           ''
