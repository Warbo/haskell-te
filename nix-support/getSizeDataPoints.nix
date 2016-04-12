{ check, equations, lib, equationCounts, sizeCounts, totalTimes }:
with builtins;
with lib;

let

# Assertions

checkIndices =
  assert all (cCount:
               assert check "Checking cCount '${cCount}'"
                            (checkCount cCount);
               assert all (checkIndex cCount) (clusterIndices cCount);
               true)
             clusterCounts;
  true;

checkIndex   = cCount: cIndex:
  assert isInt cIndex;
  assert cIndex > 0;
  assert check "${toJSON equationCounts.${cCount}} has index ${cIndex}"
               (cIndex <= length equationCounts."${cCount}");
  true;

# The sets we'll be extracting cluster-specific data from; force their
# evaluation now, to catch any lazy errors
sets =
  let result = { inherit equationCounts sizeCounts totalTimes; };
      f      = n:
        assert check "Forcing '${n}'" (isString "${toJSON result.${n}}");
        true;
   in assert all f (attrNames result);
      result;

names = attrNames sets;

checkCount  = cCount:
  assert check "isString '${toJSON cCount}'" (isString cCount);

  assert check "All isAttrs '${toJSON sets}'"
               (all (n: assert check "${n} isAttrs '${toJSON sets.${n}}'"
                                     (isAttrs sets.${n});
                        true)
                    names);

  assert all (n: assert check
                          "${n} has '${toJSON cCount}' '${toJSON sets.${n}}'"
                          (sets.${n} ? ${cCount});
                 true)
             names;

  assert all (n: assert check
                          "${n}.${cCount} isList '${toJSON sets.${n}.${cCount}}'"
                          (isList sets.${n}.${cCount});
                 true)
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
      chkLen  = n: all (m: check
                             "${n}.${cCount} length ${lengths.${n}} == ${m}.${cCount} length ${lengths.${m}}"
                             (lengths.${n}.${cCount} == lengths.${m}.${cCount}))
                       names;
   in assert all chkLen names;
      true;

# Implementation

mkPoint = cCount: cIndex: {
  eqCount       = nth cIndex equationCounts."${cCount}";
  size          = nth cIndex sizeCounts."${cCount}";
  totalTime     = nth cIndex totalTimes."${cCount}";
  clusterCount  = cCount;
};

clusterIndices = cCount: range 1 (length equations."${cCount}");

clusterCounts = attrNames equations;

pointsForCount = cCount: map (mkPoint cCount) (clusterIndices cCount);

in assert check "Checking indices for sizeDataPoints" checkIndices;
   concatMap pointsForCount clusterCounts
