{ annotate, buildPackage, callPackage, cluster, defaultClusters, drvFromScript,
  dumpPackage, explore, extractTarball, format, haskellPackages, lib,
  nixedHsPkg, nixFromCabal, pkgName, reduce, runScript, stdenv,
  storeResult, timeCalc, writeScript }:
with builtins;
with lib;

let

sum = fold (x: y: x + y) 0;

format = callPackage ./format.nix {};

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

  failed =
    let toDrv = x: if isBool x
                      then writeScript "failed" "${toString x}"
                      else x;
     in drvFromScript { fails = map toDrv [        build.failed
                                                 rawDump.failed
                                            rawAnnotated.failed
                                            rawClustered.failed
                                             rawExplored.failed
                                              rawReduced.failed ]; } ''
       FOUND_FAILURE=0
       for F in $fails
       do
         CONTENTS=$(cat "$F")
         echo "$CONTENTS" | grep "true" > /dev/null && continue

         if echo "$CONTENTS" | grep "false" > /dev/null
         then
           FOUND_FAILURE=1
           continue
         fi

         echo "Unknown boolean: $CONTENTS" 1>&2
         exit 1
       done

       if [[ "$FOUND_FAILURE" -eq 0 ]]
       then
         echo "true"  > "$out"
       else
         echo "false" > "$out"
       fi
       exit 0
     '';

  # Stick to the quick output, so testing is faster
  dump = if sampleSize == null
            then rawDump.stdout
            else runScript {} ''
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
  equationCounts = mapAttrs (_: f: drvFromScript { inherit f; } ''
                                     jq -s 'length' < "$f" > "$out"
                                   '')
                            equations;

  # Total benchmark times (split up according to clusters)
  inherit (timeCalc.pkgTimes {
            dumpTime     = rawDump.time;
            annotateTime = rawAnnotated.time;
            clusterTimes = mapAttrs (_:      v: v.time)  rawClustered.results;
            exploreTimes = mapAttrs (_: map (c: c.time)) rawExplored.results;
          })
          dynamicTimes staticTime totalTimes;
};

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
