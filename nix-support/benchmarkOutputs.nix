{ annotate, bc, buildPackage, check, cluster, defaultClusters, dumpPackage,
  explore, extractTarball, format, haskellPackages, jq, lib, nixFromCabal,
  nth, parseJSON, reduce, runScript, stdenv, storeResult, timeCalc, writeScript
}:
with builtins;
with lib;

let

sum = fold (x: y: x + y) 0;

processPkg = { clusters, quick }: name: pkg: rec {
  # Original Haskell fields
  inherit name pkg;
  src = if typeOf pkg.src == "path"
           then                pkg.src
           else extractTarball pkg.src;

  # Building with regular GHC
  build = buildPackage { inherit src quick; hsEnv = pkg.env; };

  rawDump = dumpPackage { inherit quick src; };

  rawAnnotated = annotate { inherit quick pkg;
                            asts    = dump;
                            pkgSrc  = src; };

  rawClustered = cluster { inherit annotated clusters quick; };

  # Simple format change; don't benchmark
  formatted = mapAttrs (clusterCount: clusters:
                          format clusterCount clusters)
                       clustered;

  rawExplored = explore.explore { inherit formatted quick; };

  rawReduced = reduce.reduce { inherit explored quick; };

  failed = any id [
             build.failed
             rawDump.failed
             rawAnnotated.failed
             rawClustered.failed
             rawExplored.failed
             rawReduced.failed
           ];

  # Stick to the quick output, so testing is faster
  dump      = addErrorContext "rawDump: ${toJSON rawDump}" rawDump.stdout;
  annotated = rawAnnotated.stdout;
  clustered = mapAttrs (_: v:      v.stdout)  rawClustered.results;
  explored  = mapAttrs (_: map (x: x.stdout)) rawExplored.results;
  equations = mapAttrs (_:      x: x.stdout)  rawReduced.results;

  # Useful for benchmarking
  equationCounts = mapAttrs (_: f: fromJSON (runScript {} ''
    "${jq}/bin/jq" -s 'length' < "${f}" > "$out"
  '')) equations;

  sizeCounts = mapAttrs (_: fs: sum (map (f: fromJSON (runScript {} ''
      "${jq}/bin/jq" -s 'length' < "${f}" > "$out"
    '')) fs))
    formatted;

  # Gather all values into a list of points
  sizeDataPoints = import ./getSizeDataPoints.nix {
                     inherit check equations lib equationCounts nth
                             sizeCounts totalTimes;
                     inherit (timeCalc) timeToBucket;
                   };

  # Make another list of points, with clustering runs aggregated together
  clusterDataPoints =
  assert check "isList sizeDataPoints"      (isList sizeDataPoints);
  assert check "all isAttrs sizeDataPoints" (all isAttrs sizeDataPoints);
  let
    # Combine one cluster with the others from the same run
    addTo = x: y:
      assert isInt x.eqCount;
      assert isInt y.eqCount;
      assert x.clusterCount == y.clusterCount;
      rec {
        inherit (x) clusterCount;
        eqCount    = x.eqCount + y.eqCount;
        totalTime  = timeCalc.sumTimes [x.totalTime  y.totalTime];
        timeBucket = timeCalc.timeToBucket totalTime;
      };

    # Given a new point, partition the previous points into those from the
    # same run ("right") and those from other runs ("wrong"). If there's a
    # "right" point add the new one to it; otherwise use the new point as-is
    accum = newP: old:
      assert check "isList  ${toJSON old}"     (isList  old);
      assert check "isAttrs ${toJSON newP}"    (isAttrs newP);
      assert check "all isAttrs ${toJSON old}" (all isAttrs old);
      assert check "newP has clusterCount ${toJSON newP}" (newP ? clusterCount);
      assert check "Old points have clusterCount ${toJSON old}"
                   (all (p: p ? clusterCount) old);
      with partition (oldP: oldP.clusterCount == newP.clusterCount) old;
      assert (length right < 2);
      wrong ++ (if length right == 1
                   then [(addTo newP (head right))]
                   else [newP]);
  in fold accum [] sizeDataPoints;

  # Total benchmark times (split up according to clusters)
  inherit (timeCalc.pkgTimes {
            dumpTime     = rawDump.time;
            annotateTime = rawAnnotated.time;
            clusterTimes = mapAttrs (_:      v: v.time)  rawClustered.results;
            exploreTimes = mapAttrs (_: map (c: c.time)) rawExplored.results;
          })
          dynamicTimes staticTime totalTimes;
};

forceVal = x: msg: check msg (isString "${toJSON x}");

forceAttr = p: a:
  assert isAttrs p;
  assert isString a;
  assert check "Looking for attribute '${a}'" (p ? "${a}");
  assert forceVal p."${a}" "Forcing attribute '${a}' of type ${typeOf p.${a}}";
  true;

processedOrFailed = p: if p.failed then p
                                   else checkProcessed p;

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

processCheck = args: name: pkg: processedOrFailed (processPkg args name pkg);

basic = clusters: quick: mapAttrs (processCheck { inherit clusters quick; })
                                  haskellPackages;

bootstraps = clusters: quick: mapAttrs (processCheck { inherit clusters quick; })
                                       bootstrapped;

bootstrapped =
  let src = extractTarball "${toString haskellPackages.ghc.src}";
   in {
     base =
       let patched = stdenv.mkDerivation {
             name    = "base-src";
             builder = writeScript "base-patcher" ''
               source $stdenv/setup
               set -e
               cp -r "${src}/libraries/base" .
               chmod -R +w base

               patch base/base.cabal << EndOfPatch
               58c58
               <     Default: False
               ---
               >     Default: True
               EndOfPatch

               cp -r base "$out"
             '';
           };
           p = haskellPackages.callPackage
                 (nixFromCabal "${patched}" null)
                 {};
        in p // { name = "base"; pkg = p; };
  };

in {
  processPackage  = { clusters ? defaultClusters, quick }:
                        processCheck { inherit clusters quick; };
  processPackages = { clusters ? defaultClusters, quick }:
                      basic clusters quick // bootstraps clusters quick;
}
