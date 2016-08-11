defs: with defs; pkg:

{
  formattedAttrs   = testMsg (isAttrs pkg.formatted) "attrs formatted";

  formattedStrings = testMsg (all (n: isString n)
                                  (attrNames pkg.formatted))
                             "All formatted keys are strings";

  formattedInts    = testMsg (all (n: isInt (fromJSON n))
                                  (attrNames pkg.formatted))
                             "All 'formatted' keys are ints";

  formattedLists   = testMsg (all (n: isList pkg.formatted."${n}")
                                  (attrNames pkg.formatted))
                             "All 'formatted' values are lists";

  formattedStrings = testMsg (all (n: all isString pkg.formatted."${n}")
                                  (attrNames pkg.formatted))
                             "All 'formatted' keys are strings";

  exploredAttrs  = testMsg (isAttrs pkg.rawExplored) "explored is set";

  exploredInts   = testMsg (all (n: isInt  (fromJSON n))
                                (attrNames pkg.rawExplored))
                           "explored keys are numeric";

  exploredLists  = testMsg (all (n: isList pkg.rawExplored."${n}")
                                (attrNames pkg.rawExplored))
                           "explored values are lists";

  exploredSets   = testMsg (all (n: all isAttrs pkg.rawExplored."${n}")
                                (attrNames pkg.rawExplored))
                           "explored values contain sets";

  exploredStdout = testMsg (all (n: all (x: x ? stdout) pkg.rawExplored."${n}")
                                (attrNames pkg.rawExplored))
                           "explored values have stdout";

  exploredTimes  = testMsg (all (n: all (x: x ? time) pkg.rawExplored."${n}")
                                (attrNames pkg.rawExplored))
                           "explored values have time";
}
