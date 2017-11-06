# All of our "global" definitions live here (i.e. everything that's used in more
# than one place). Note that care should be taken to avoid infinite loops, since
# 'callPackage' gets arguments from 'self', which is the set we're defining!
{
  lib    ? (import (import ./path.nix {}) {}).lib,
  stable ? true,
  ...
}@args:

with builtins;
with lib;

fix (self: rec {
  # Various versions of nixpkgs from which to get our packages
  inherit (import ./nixpkgs.nix args)
    # Whichever nixpkgs we're using by default (depending on 'stable')
    nixpkgs nixpkgs-src

    # Fixed releases of nixpkgs. Useful for avoiding known incompatibilities.
    nixpkgs-2016-03 nixpkgs-2016-09

    # Default nixpkgs, overridden with helper functions and packages
    nix-config nix-config-src;

  # Regular dependencies, used as-is
  inherit (nixpkgs)
    bash buildEnv cabal-install glibcLocales jq lib runCommand stdenv utillinux
    writeScript;

  # Fixed versions to avoid known breakages
  inherit (nixpkgs-2016-03)
    # Args differ in new versions, which breaks ./haskellPackages.nix scripts
    cabal2nix;

  inherit (nixpkgs-2016-09)
    # The quoting is different in other versions, which breaks e.g. wrap
    makeWrapper

    # Old versions don't have the needed contracts, new ones don't build on i686
    racket;

  # Helper functions, etc.
  inherit (nix-config)
    allDrvsIn attrsToDirs backtrace fail mkBin nixListToBashArray nothing
    pipeToNix reverse sanitiseName stable stripOverrides timeout unlines unpack
    withDeps wrap;

  # Cases where we want both the attribute set and its attributes available
  inherit (callPackage ./annotate.nix {})
    annotated annotateRawAstsFrom;
  inherit (dumpToNixScripts)
    dumpToNix;
  inherit (runTypesScriptData)
    runTypesScript;

  # Imports a file and calls the function it contains, automatically looking up
  # argument values from the 'self' attrset.
  callPackage = nixpkgs.callPackage ./callPackage.nix { inherit self; };

  analysis              = callPackage ./analysis.nix              {};
  asv-nix               = callPackage ./asv-nix.nix               {};
  buckets               = callPackage ./buckets.nix               {};
  callHackage           = callPackage ./callHackage.nix           {};
  checkHsEnv            = callPackage ./checkHsEnv.nix            {};
  checkStderr           = callPackage ./checkStderr.nix           {};
  cluster               = callPackage ./cluster.nix               {};
  concurrentQuickspec   = callPackage ./concurrentQuickspec.nix   {};
  dumpToNixScripts      = callPackage ./dumpToNix.nix             {};
  extractedEnv          = callPackage ./extractedEnv.nix          {};
  extraHaskellPackages  = callPackage ./extraHaskellPackages.nix  {};
  filterToSampled       = callPackage ./filterToSampled.nix       {};
  format                = callPackage ./format.nix                {};
  genQuickspecRunner    = callPackage ./genQuickspecRunner.nix    {};
  getDepsScript         = callPackage ./getDepsScript.nix         {};
  haskellPackages       = callPackage ./haskellPackages.nix       {};
  haskellPkgNameVersion = callPackage ./haskellPkgNameVersion.nix {};
  haskellPkgToAsts      = callPackage ./haskellPkgToAsts.nix      {};
  haskellPkgToRawAsts   = callPackage ./haskellPkgToRawAsts.nix   {};
  haveVar               = callPackage ./haveVar.nix               {};
  hsNameVersion         = callPackage ./hsNameVersion.nix         {};
  hsOverride            = callPackage ./hsOverride.nix            {};
  inNixedDir            = callPackage ./inNixedDir.nix            {};
  makeHaskellPkgNixable = callPackage ./makeHaskellPkgNixable.nix {};
  ML4HSFE               = callPackage ./ML4HSFE.nix               {};
  nixedHsPkg            = callPackage ./nixedHsPkg.nix            {};
  nixEnv                = callPackage ./nixEnv.nix                {};
  nixFromCabal          = callPackage ./nixFromCabal.nix          {};
  nixify                = callPackage ./nixify.nix                {};
  package               = callPackage ./package.nix               {};
  pkgName               = callPackage ./pkgName.nix               {};
  quickspec             = callPackage ./quickspec.nix             {};
  quickspecAsts         = callPackage ./quickspecAsts.nix         {};
  reduce-equations      = callPackage ./reduce-equations.nix      {};
  renderEqs             = callPackage ./renderEqs.nix             {};
  runTypesScriptData    = callPackage ./runTypesScript.nix        {};
  runWeka               = callPackage ./runWeka.nix               {};
  sta                   = callPackage ./sta.nix                   {};
  testData              = callPackage ./testData.nix              {};
  tipBenchmarks         = callPackage ./tipBenchmarks.nix         {};
  tipToHaskellPkg       = callPackage ./tipToHaskellPkg.nix       {};
  tryElse               = callPackage ./tryElse.nix               {};
  tryTip                = callPackage ./tryTip.nix                {};
  withNix               = callPackage ./withNix.nix               {};
})
