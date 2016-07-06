{ doCheck, equations, lib, equationCounts, nth, sizeCounts,
  timeToBucket, totalTimes }:
with builtins;
with lib;

let

# The sets we'll be extracting cluster-specific data from; force their
# evaluation now, to catch any lazy errors
sets = let result = { inherit equationCounts sizeCounts totalTimes; };
           f      = n: assert doCheck "Forcing '${n}'"
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
#      doCheck "Trying foo" (doCheck "Attr 'bar' in ${toJSON baz}" (baz ? bar))
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
               assert doCheck "Checking cCount '${cCount}'"
                            (checkCount cCount);
               assert checkAttr cCount;
               true)
             clusterCounts;
  true;

checkAttr   = cCount:
  assert doCheck "${toJSON equationCounts} has attr ${cCount}"
               (equationCounts ? "${cCount}");
  true;

checkCount  = cCount:
  assert doCheck "isString '${toJSON cCount}'" (isString cCount);

  assert doCheck "All isAttrs '${toJSON sets}'"
               (all (n: assert doCheck "${n} isAttrs '${toJSON sets.${n}}'"
                                     (isAttrs sets."${n}");
                        true)
                    names);

  assert all (n: assert doCheck
                          "${n} has '${toJSON cCount}' '${toJSON sets.${n}}'"
                          (sets."${n}" ? "${cCount}");
                 true)
             names;

  true;

checkSet = s:
  assert doCheck "isAttrs '${toJSON s}'" (isAttrs s);
  assert all (cCount: assert doCheck "Attr ${cCount} in ${toJSON s}"
                                   (s ? "${cCount}");
                      true)
             clusterCounts;
  true;

checkList = l:
  assert doCheck "isList '${toJSON l}'" (isList l);
  true;

checkPoints = all checkPoint allPoints;

checkPoint = p:
  assert doCheck "Point type ${typeOf p} == set" (isAttrs p);
  assert all (n: doCheck "Point contains ${n}" (p ? "${n}"))
                 ["eqCount" "size" "totalTime" "timeBucket"
                  "clusterCount"];
  assert isInt p.eqCount;
  true;

# Implementation

mkPoint = cCount: rec {
  eqCount       = equationCounts."${cCount}";
  size          = sizeCounts."${cCount}";
  totalTime     = totalTimes."${cCount}";
  timeBucket    = timeToBucket totalTime;
  clusterCount  = cCount;
};

clusterCounts = addErrorContext "clusterCounts from ${toJSON equations}"
                                (attrNames equations);

allPoints = map mkPoint clusterCounts;

in

# Check inputs
assert doCheck "Checking equations"      (checkSet equations);
assert doCheck "Checking equationCounts" (checkSet equationCounts);
assert doCheck "Checking sizeCounts"     (checkSet sizeCounts);
assert doCheck "Checking totalTimes"     (checkSet totalTimes);

assert doCheck "Checking points"                     (checkList allPoints);
assert doCheck "Checking each point"                 checkPoints;
assert doCheck "Checking indices for sizeDataPoints" checkIndices;

allPoints
