{ annotate, bc, buildPackage, check, cluster, dumpPackage, explore,
  extractTarball, format, haskellPackages, jq, lib, nth, parseJSON, runScript,
  timeCalc }:
with builtins;
with lib;

{ clusters }: { quick }:

let

sum = fold (x: y: x + y) 0;

processPkg = name: pkg: rec {
  # Original Haskell fields
  inherit name pkg;
  src = extractTarball pkg.src;

  # Building with regular GHC
  build = buildPackage { inherit src quick; hsEnv = pkg.env; };

  rawDump = dumpPackage { inherit quick src; };

  rawAnnotated = annotate { inherit quick;
                            asts    = dump;
                            pkgName = name; };

  rawClustered = cluster { inherit annotated clusters quick; };

  # Simple format change; don't benchmark
  formatted = mapAttrs (clusterCount: clusters:
                          format clusterCount clusters)
                       clustered;

  rawExplored = explore { inherit formatted quick; };

  # Stick to the quick output, so testing is faster
  dump      = rawDump.stdout;
  annotated = rawAnnotated.stdout;
  clustered = mapAttrs (_: v: v.stdout) rawClustered;
  explored  =
    assert check "rawExplored isAttrs '${toJSON rawExplored}'"
                 (isAttrs rawExplored);
    assert check "All rawExplored are lists '${toJSON rawExplored}'"
                 (all (n:     isList  rawExplored.${n}) (attrNames rawExplored));
    assert check "All rawExplored.X contain sets '${toJSON rawExplored}'"
                 (all (n: all isAttrs rawExplored.${n}) (attrNames rawExplored));
    mapAttrs (_: map (x: x.stdout)) rawExplored;
  equations = trace "FIXME: Reduce equations" explored;

  # Useful for benchmarking
  equationCounts = mapAttrs (_: map (f: fromJSON (runScript {} ''
    "${jq}/bin/jq" -s 'length' < "${f}" > "$out"
  ''))) equations;

  sizeCounts = mapAttrs (_: map (f: fromJSON (runScript {} ''
      "${jq}/bin/jq" -s 'length' < "${f}" > "$out"
    '')))
    formatted;

  # Gather all values into a list of points
  sizeDataPoints = import ./getSizeDataPoints.nix {
                     inherit check equations lib equationCounts nth
                             sizeCounts totalTimes;
                   };

  # Make another list of points, with clustering runs aggregated together
  clusterDataPoints = let
    # Combine one cluster with the others from the same run
    addTo = x: y: {
      eqCount = x.eqCount + y.eqCount;
    };
    # Given a new point, partition the previous points into those from the
    # same run ("right") and those from other runs ("wrong"). If there's a
    # "right" point add the new one to it; otherwise use the new point as-is
    accum = newP: old:
      with partition (oldP: oldP.clusterCount == newP.clusterCount) old;
      assert (length right < 2);
      wrong ++ (if length right == 1
                   then [addTo newP (head right)]
                   else [newP]);
  in fold accum [] sizeDataPoints;

  # Total benchmark times (split up according to clusters)
  inherit (timeCalc {
            dumpTime     = rawDump.time;
            annotateTime = rawAnnotated.time;
            clusterTimes = mapAttrs (_:      v: v.time)  rawClustered;
            exploreTimes = mapAttrs (_: map (c: c.time)) rawExplored;
          })
          dynamicTimes staticTime totalTimes;
};

forceVal = x: msg: check msg (isString "${toJSON x}");

forceAttr = p: a:
  assert isAttrs p;
  assert isString a;
  assert check "Looking for attribute '${a}'" (p ? ${a});
  assert forceVal p.${a} "Forcing attribute '${a}'";
  true;

checkProcessed = p:
  assert isAttrs p;
  assert p ? pkg;

  # Force particular parts of our output, to expose any latent errors
  assert forceAttr p "name";
  assert forceAttr p "build";
  assert forceAttr p "dump";
  assert forceAttr p "annotated";
  assert forceAttr p "formatted";
  assert forceAttr p "clustered";
  assert forceAttr p "explored";
  assert forceAttr p "equations";
  assert forceAttr p "equationCounts";
  assert forceAttr p "sizeCounts";
  assert forceAttr p "dynamicTimes";
  assert forceAttr p "staticTime";
  assert forceAttr p "totalTimes";
  assert forceAttr p "sizeDataPoints";

  p;

processCheck = name: pkg: checkProcessed (processPkg name pkg);

in mapAttrs processCheck haskellPackages
