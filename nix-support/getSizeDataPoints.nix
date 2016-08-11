{ ourCheck, equations, lib, equationCounts, nth, sizeCounts, totalTimes }:
with builtins;
with lib;

let

# The sets we'll be extracting cluster-specific data from; force their
# evaluation now, to catch any lazy errors
sets = let result = { inherit equationCounts sizeCounts totalTimes; };
           f      = n: assert ourCheck "Forcing '${n}'"
                                    (isString "${toJSON result.${n}}");
                       true;
        in assert all f (attrNames result);
           result;

names = attrNames sets;

# Assertions. Since we're juggling rows, columns, etc. there are many
# opportunities to make a type-safe mistake, so we make extra double sure that
# everything makes sense.

# Two aspects of laziness to keep in mind:
#
#  - We may be given a datastructure containing errors, which will fire when
#    those parts are forced. We can force the whole datastructure using 'toJSON'
#    in our error messages. Since such error messages may trigger errors, we
#    should wrap them in an outer message, e.g.
#
#      ourCheck "Trying foo" (ourCheck "Attr 'bar' in ${toJSON baz}" (baz ? bar))
#
#    If the 'baz ? bar' check fails, we get "Attr 'bar' in ..." in the trace.
#    If 'toJSON' triggers an error in 'baz', we get "Trying foo" in the trace.
#
#  - Our checks may accumulate in large, lazy datastructures, never to be run,
#    or forced from somewhere completely out of context. To ensure our checks
#    are made as soon as possible, and as close to their source location as
#    possible, we use an 'assert foo; true' style. By nesting uses of 'assert',
#    rather than just returning booleans, we guide Nix's evaluation order down
#    through nested checks, discard any data used by the check as soon as it's
#    passed, and fail as close to the error location as we can.

checkIndices =
  assert all (cCount:
               assert ourCheck "Checking cCount '${cCount}'"
                            (checkCount cCount);
               assert checkAttr cCount;
               true)
             clusterCounts;
  true;

checkAttr   = cCount:
  assert ourCheck "${toJSON equationCounts} has attr ${cCount}"
               (equationCounts ? "${cCount}");
  true;

checkCount  = cCount:
  assert ourCheck "isString '${toJSON cCount}'" (isString cCount);

  assert ourCheck "All isAttrs '${toJSON sets}'"
               (all (n: assert ourCheck "${n} isAttrs '${toJSON sets.${n}}'"
                                     (isAttrs sets."${n}");
                        true)
                    names);

  assert all (n: assert ourCheck
                          "${n} has '${toJSON cCount}' '${toJSON sets.${n}}'"
                          (sets."${n}" ? "${cCount}");
                 true)
             names;

  true;

checkSet = s:
  assert ourCheck "isAttrs '${toJSON s}'" (isAttrs s);
  assert all (cCount: assert ourCheck "Attr ${cCount} in ${toJSON s}"
                                   (s ? "${cCount}");
                      true)
             clusterCounts;
  true;

checkList = l:
  assert ourCheck "isList '${toJSON l}'" (isList l);
  true;

checkPoints = all checkPoint allPoints;

checkPoint = p:
  assert ourCheck "Point type ${typeOf p} == set" (isAttrs p);
  assert all (n: ourCheck "Point contains ${n}" (p ? "${n}"))
                 ["eqCount" "size" "totalTime" "clusterCount"];
  assert isInt p.eqCount;
  true;

# Implementation

mkPoint = cCount: rec {
  eqCount       = equationCounts."${cCount}";
  size          = sizeCounts."${cCount}";
  totalTime     = totalTimes."${cCount}";
  clusterCount  = cCount;
};

clusterCounts = addErrorContext "clusterCounts from ${toJSON equations}"
                                (attrNames equations);

allPoints = map mkPoint clusterCounts;

in

# Check inputs
assert ourCheck "Checking equations"      (checkSet equations);
assert ourCheck "Checking equationCounts" (checkSet equationCounts);
assert ourCheck "Checking sizeCounts"     (checkSet sizeCounts);
assert ourCheck "Checking totalTimes"     (checkSet totalTimes);

assert ourCheck "Checking points"                     (checkList allPoints);
assert ourCheck "Checking each point"                 checkPoints;
assert ourCheck "Checking indices for sizeDataPoints" checkIndices;

allPoints
