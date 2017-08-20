defs: with defs; pkg:

with builtins;
with lib;

{
  formattedAttrs   = testMsg (isAttrs pkg.formatted) "attrs formatted";

  formattedInts    = mapAttrs (n: v: testMsg (isInt (fromJSON n))
                                             "All 'formatted' keys are ints")
                              pkg.formatted;

  formattedLists   = mapAttrs (n: v: testMsg (isList v)
                                             "All 'formatted' values are lists")
                              pkg.formatted;

  formattedEntries = mapAttrs (n: v: testMsg (all isAttrs v)
                                             "All 'formatted' list entries are attrs")
                              pkg.formatted;

  exploredInts   = mapAttrs (n: v: testMsg (isInt (fromJSON n))
                                           "explored key ${n} is numeric")
                            pkg.rawExplored.results;

  exploredLists  = mapAttrs (n: v: testMsg (isList v)
                                           "Have list ${n}")
                            pkg.rawExplored.results;

  exploredSets   = mapAttrs (n: v: testMsg (all isAttrs v) "All ${n} attrs")
                            pkg.rawExplored.results;

  exploredStdout = mapAttrs (n: v: testMsg (all (x: x ? stdout) v)
                                           "explored values have stdout")
                            pkg.rawExplored.results;
}
