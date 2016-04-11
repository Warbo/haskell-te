{ annotate, assertMsg, bc, buildPackage, cluster, dumpPackage, explore,
  extractTarball, format, haskellPackages, jq, lib, parseJSON, runScript,
  timeCalc }:
with builtins;
with lib;
with timeCalc;

{ clusters }: { quick }:

let sum = fold (x: y: x + y) 0;
    nth = n: lst: if n == 0 then head lst else nth (n - 1) (tail lst);
    processPkg       = name: pkg:
      let result = rec {
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
          assert assertMsg (isAttrs rawExplored)
                           "rawExplored isAttrs '${toJSON rawExplored}'";
          assert assertMsg (all (n:     isList  rawExplored.${n}) (attrNames rawExplored))
                           "All rawExplored are lists '${toJSON rawExplored}'";
          assert assertMsg (all (n: all isAttrs rawExplored.${n}) (attrNames rawExplored))
                           "All rawExplored.X contain sets '${toJSON rawExplored}'";
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
                           inherit assertMsg equations lib equationCounts
                                   sizeCounts totalTime;
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
        staticTime = sumTimes [ rawDump.time rawAnnotated.time ];

        dynamicTime = mapAttrs (c: _: map (n: sumTimes [
                                        (nth n rawClustered."${c}")
                                        (nth n rawExplored."${c}")
                                      ])) equations;

        totalTime = mapAttrs (c: map (t: sumTimes [t staticTime]))
                                 dynamicTime;
      };
    in assert isAttrs result;
       result;
 in mapAttrs processPkg haskellPackages
