args:

# Fetch known revisions of nixpkgs, so our 'stable' configuration isn't at the
# mercy of system updates
with import ./nixpkgs.nix args;
with nixpkgs.lib;
with builtins;

# All of our "global" definitions live here (i.e. everything that's used in more
# than one place). Note that care should be taken to avoid infinite loops, since
# 'callPackage' gets arguments from 'self', which is the set we're defining!
fix (self: rec {
  # Bring in some stuff as-is from nixpkgs
  inherit (nixpkgs)
    bash buildEnv cabal-install glibcLocales jq lib runCommand utillinux
    writeScript;

  # These packages have hard-coded versions, since newer ones are known to be
  # incompatible

  inherit (nixpkgs-2016-03)
    # Args differ in new versions, which breaks ./haskellPackages.nix scripts
    cabal2nix;

  inherit (nixpkgs-2016-09)
    # Use newer makeWrapper for quoting changes
    makeWrapper

    # Old versions don't have the needed contracts, new ones don't build on i686
    racket;


  inherit (nixpkgs.callPackage ./nixFromCabal.nix { inherit cabal2nix; })
    nixedHsPkg nixFromCabal;

  # We have many custom Haskell packages, and also need particular versions of
  # regular Haskell packages in order to satisfy dependencies.
  inherit (callPackage ./haskellPackages.nix {
            callHackage          = nixpkgs.callPackage ./callHackage.nix {};
            superHaskellPackages = nixpkgs.haskellPackages;
          })
    haskellPackages hsOverride;

  # Include the above definitions
  inherit nix-config nix-config-src nixpkgs-2016-09 nixpkgs-src;

  inherit (nix-config)
    allDrvsIn attrsToDirs backtrace fail inNixedDir mkBin nixListToBashArray
    nothing pipeToNix reverse sanitiseName stripOverrides timeout unpack
    withDeps wrap;

  # These provide executables
  inherit (haskellPackages)
    AstPlugin GetDeps ML4HSFE mlspec reduce-equations;

  inherit (callPackage ./test-defs.nix {})
          runTestInDrv testAll testDbg testDrvString testFiles testMsg
          testPackages testRec testRun testWrap;

  annotateRawAstsFrom   = callPackage ./annotateRawAstsFrom.nix   {};
  annotateScripts       = callPackage ./annotate.nix              {};
  asv-nix               = callPackage ./asv-nix.nix               {};
  bashEscape            = callPackage ./bashEscape.nix            {};
  benchmarkEnv          = callPackage ./benchmarkEnv.nix          {};
  buckets               = callPackage ./buckets.nix               {};
  cacheContent          = callPackage ./cacheContent.nix          {};
  checkHsEnv            = callPackage ./checkHsEnv.nix            {};
  checkStderr           = callPackage ./checkStderr.nix           {};
  cluster               = callPackage ./cluster.nix               {};
  dumpToNixScripts      = callPackage ./dumpToNix.nix             {};
  explore               = callPackage ./explore.nix               {};
  extractTarball        = callPackage ./extractTarball.nix        {};
  filterToSampled       = callPackage ./filterToSampled.nix       {};
  format                = callPackage ./format.nix                {};
  genQuickspecRunner    = callPackage ./genQuickspecRunner.nix    {};
  getDepsScript         = callPackage ./getDepsScript.nix         {};
  hashspecBench         = callPackage ./hashspecBench.nix         {};
  haskellPkgNameVersion = callPackage ./haskellPkgNameVersion.nix {};
  haskellPkgToAsts      = callPackage ./haskellPkgToAsts.nix      {};
  haskellPkgToRawAsts   = callPackage ./haskellPkgToRawAsts.nix   {};
  haveVar               = callPackage ./haveVar.nix               {};
  hsNameVersion         = callPackage ./hsNameVersion.nix         {};
  importDir             = callPackage ./importDir.nix             {};
  makeHaskellPkgNixable = callPackage ./makeHaskellPkgNixable.nix {};
  mlspecBench           = callPackage ./mlspecBench.nix           {};
  nixify                = callPackage ./nixify.nix                {};
  package               = callPackage ./package.nix               {};
  parseJSON             = callPackage ./parseJSON.nix             {};
  pkgName               = callPackage ./pkgName.nix               {};
  quickspec             = callPackage ./quickspec.nix             {};
  quickspecAsts         = callPackage ./quickspecAsts.nix         {};
  runCmd                = callPackage ./runBenchmark.nix          {};
  runScript             = callPackage ./runScript.nix             {};
  runTypes              = callPackage ./runTypes.nix              {};
  runTypesScriptData    = callPackage ./runTypesScript.nix        {};
  runWeka               = callPackage ./runWeka.nix               {};
  sta                   = callPackage ./sta.nix                   {};
  testData              = callPackage ./testData.nix              {};
  tipBenchmarks         = callPackage ./tipBenchmarks.nix         {};
  tipToHaskellPkg       = callPackage ./tipToHaskellPkg.nix       {};
  tryElse               = callPackage ./tryElse.nix               {};

  annotated = pkgDir: annotate rec {
    pkg    = { name = "dummy"; };
    asts   = dumpToNix { pkgDir = pkgSrc; };
    pkgSrc = nixedHsPkg pkgDir;
  };

  annotate       = annotateScripts.annotate;
  callPackage    = nixpkgs.newScope self;
  dumpToNix      = dumpToNixScripts.dumpToNix;
  runTypesScript = runTypesScriptData.runTypesScript;
  stable         = args.stable or true;
  unlines        = concatStringsSep "\n";

  drvFromScript =  nixpkgs.callPackage ./drvFromScript.nix { inherit withNix; };
  nixEnv        = (nixpkgs.callPackage ./nixEnv.nix        {}) null;
  withNix       =  nixpkgs.callPackage ./withNix.nix       { inherit nixEnv;  };
})
