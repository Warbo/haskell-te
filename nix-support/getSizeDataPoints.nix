{ assertMsg, equations, lib, equationCounts, sizeCounts, totalTime }:
with builtins;
with lib;

let

# Assertions

checkIndices = all (cCount:
                     assert assertMsg (checkCount cCount)
                                      "Checking cCount '${cCount}'";
                     all (checkIndex cCount) (clusterIndices cCount))
                   clusterCounts;
checkIndex   = cCount: cIndex:
  assert isInt cIndex;
  assert cIndex > 0;
  assert assertMsg (cIndex <= length equationCounts."${cCount}")
                   "${toJSON equationCounts.${cCount}} has index ${cIndex}";
  true;

# The sets we'll be extracting cluster-specific data from; force their
# evaluation now, to catch any lazy errors
sets =
  let result = { inherit equationCounts sizeCounts totalTime; };
      f      = n: assertMsg (isString "${toJSON result.${n}}") "Forcing '${n}'";
   in assert all f (attrNames result);
      result;

names = attrNames sets;

checkCount  = cCount:
  assert assertMsg (isString cCount) "isString '${toJSON cCount}'";

  assert assertMsg (all (n: assertMsg (isAttrs sets.${n})
                                      "${n} isAttrs '${toJSON sets.${n}}'")
                        names)
                   "All isAttrs '${toJSON sets}'";

  assert all (n: assertMsg
                   (sets.${n} ? ${cCount})
                   "${n} has '${toJSON cCount}' '${toJSON sets.${n}}'")
             names;

  assert all (n: assertMsg
                   (isList sets.${n}.${cCount})
                   "${n}.${cCount} isList '${toJSON sets.${n}.${cCount}}'")
             names;

  assert checkLen cCount;

  true;

# For all n and m, sets.n.cCount has the same length as sets.m.cCount
checkLen = cCount:
  let lengths = fold (n: old: old // {
                       ${n} = length sets.${n}.${cCount};
                     })
                     {}
                     names;
      chkLen  = n: all (m: assertMsg
                             (lengths.${n}.${cCount} == lengths.${m}.${cCount})
                             "${n}.${cCount} length ${lengths.${n}} == ${m}.${cCount} length ${lengths.${m}}")
                       names;
   in assert all checkLen names;
      true;

# Implementation

mkPoint = cCount: cIndex: {
  eqCount       = nth cIndex equationCounts."${cCount}";
  size          = nth cIndex sizeCounts."${cCount}";
  totalTime     = nth cIndex totalTime."${cCount}";
  clusterCount  = cCount;
};

clusterIndices = cCount: range 1 (length equations."${cCount}");

clusterCounts = attrNames equations;

pointsForCount = cCount: map (mkPoint cCount) (clusterIndices cCount);

in assert assertMsg checkIndices "Checking indices for sizeDataPoints";
   concatMap pointsForCount clusterCounts
