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

  formattedKeys = mapAttrs (n: v: testMsg (all isString v)
                                          "All 'formatted' keys are strings")
                           pkg.formatted;

  exploredAttrs  = testMsg (isAttrs pkg.rawExplored.results) "explored is set";

  exploredInts   = mapAttrs (n: v: testMsg (isInt (fromJSON n))
                                           "explored key ${n} is numeric")
                            pkg.rawExplored.results;

  exploredLists  = mapAttrs (n: v: isList v) pkg.rawExplored.results;

  exploredSets   = mapAttrs (n: v: testMsg (all isAttrs v) "All ${n} attrs")
                            pkg.rawExplored.results;

  exploredStdout = mapAttrs (n: v: testMsg (all (x: x ? stdout) v)
                                           "explored values have stdout")
                            pkg.rawExplored.results;

  exploredTimes  = mapAttrs (n: v: testMsg (all (x: x ? time) v)
                                           "explored values have time")
                            pkg.rawExplored.results;
}
