{ annotate, bc, buildPackage, ourCheck, cluster, defaultClusters, dumpPackage,
  explore, extractTarball, format, haskellPackages, jq, lib, nixedHsPkg,
  nixFromCabal, nth, parseJSON, pkgName, reduce, runScript, stdenv, storeResult,
  timeCalc, writeScript
}:
with builtins;
with lib;

let

sum = fold (x: y: x + y) 0;

processPkg = { clusters, quick, sampleSize ? null }: givenName: givenPkg: rec {
  # Original Haskell fields
  pkg  = givenPkg // { inherit name; };
  name = pkgName givenName;

  # Extract tarballs if necessary
  src = if typeOf pkg.src == "path"
           then                pkg.src
           else extractTarball pkg.src;

  # Run cabal2nix if necessary
  srcNixed = if pathExists (unsafeDiscardStringContext "${src}/default.nix")
                then src
                else nixedHsPkg "${src}" null;

  # Building with regular GHC
  build = buildPackage { inherit src quick; hsEnv = pkg.env; };

  rawDump = dumpPackage { inherit quick src; };

  rawAnnotated = annotate { inherit quick pkg;
                            asts   = dump;
                            pkgSrc = srcNixed; };

  rawClustered = cluster { inherit annotated clusters quick; };

  # Simple format change; don't benchmark
  formatted = mapAttrs format clustered;

  rawExplored = explore.explore {
                  inherit formatted quick;
                  standalone = srcNixed;
                };

  rawReduced = reduce.reduce { inherit explored quick; };

  failed = any (x: if isBool x
                      then x
                      else import "${x}") [
             build.failed
             rawDump.failed
             rawAnnotated.failed
             rawClustered.failed
             rawExplored.failed
             rawReduced.failed
           ];

  # Stick to the quick output, so testing is faster
  dump = if sampleSize == null
            then rawDump.stdout
            else runScript { buildInputs = [ jq ]; } ''
                   # Sample from quickspecable definitions
                   cat "${rawDump.stdout}"                   |
                   jq -c 'map(select(.quickspecable)) | .[]' |
                   shuf                                      |
                   head -n${toString sampleSize}             > fg

                   # Include the un-quickspecable "background"
                   cat "${rawDump.stdout}"                         |
                   jq -c 'map(select(.quickspecable | not)) | .[]' > bg

                   cat fg bg | jq -s '.' > out

                   "${storeResult}" out
                 '';
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
                     inherit ourCheck equations lib equationCounts nth
                             sizeCounts totalTimes;
                   };

  # Make another list of points, with clustering runs aggregated together
  clusterDataPoints =
  assert ourCheck "isList sizeDataPoints"      (isList sizeDataPoints);
  assert ourCheck "all isAttrs sizeDataPoints" (all isAttrs sizeDataPoints);
  let
    # Combine one cluster with the others from the same run
    addTo = x: y:
      assert isInt x.eqCount;
      assert isInt y.eqCount;
      assert x.clusterCount == y.clusterCount;
      rec {
        inherit (x) clusterCount;
        eqCount    = x.eqCount + y.eqCount;
        totalTime  = timeCalc.sumTimeDrvs [x.totalTime  y.totalTime];
      };

    # Given a new point, partition the previous points into those from the
    # same run ("right") and those from other runs ("wrong"). If there's a
    # "right" point add the new one to it; otherwise use the new point as-is
    accum = newP: old:
      assert ourCheck "isList  ${toJSON old}"     (isList  old);
      assert ourCheck "isAttrs ${toJSON newP}"    (isAttrs newP);
      assert ourCheck "all isAttrs ${toJSON old}" (all isAttrs old);
      assert ourCheck "newP has clusterCount ${toJSON newP}" (newP ? clusterCount);
      assert ourCheck "Old points have clusterCount ${toJSON old}"
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

forceVal = x: msg: ourCheck msg (isString "${toJSON x}");

forceAttr = p: a:
  assert isAttrs p;
  assert isString a;
  assert ourCheck "Looking for attribute '${a}'" (p ? "${a}");
  assert forceVal p."${a}" "Forcing attribute '${a}' of type ${typeOf p.${a}}";
  true;

checkProcessed = p:
  assert isAttrs p;
  assert p ? pkg;
  p;

processCheck = args: name: pkg: checkProcessed (processPkg args name pkg);

basic = clusters: quick: sampleSize: mapAttrs (processCheck { inherit clusters quick sampleSize; })
                                  haskellPackages;

bootstraps = clusters: quick: sampleSize: mapAttrs (processCheck { inherit clusters quick sampleSize; })
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
  processPackage  = { clusters ? defaultClusters, quick, sampleSize ? null }:
                        processCheck { inherit clusters quick sampleSize; };
  processPackages = { clusters ? defaultClusters, quick, sampleSize ? null }:
                      basic clusters quick sampleSize // bootstraps clusters quick sampleSize;
}
