# All of our "global" definitions live here (i.e. everything that's used in more
# than one place). Note that care should be taken to avoid infinite loops, since
# 'callPackage' gets arguments from 'self', which is the set we're defining!
self: super:

with builtins;
#with super.lib;
with {
  helpersSrc = import ./nix-support/helpers.nix {
    inherit (import (import ./nix-support/path.nix {}) {}) fetchFromGitHub;
  };
};
{
  tePath = import ./nix-support/path.nix {};

  helpers =
    with import self.tePath {
      overlays = [
        (import "${helpersSrc}/overlay.nix")
        (import ./overlay.nix)
      ];
    };
    nix-helpers;

  inherit helpersSrc;

  # Various versions of nixpkgs from which to get our packages
  inherit (import ./nix-support/nixpkgs.nix)
    # Whichever nixpkgs we're using by default
    nixpkgs

    # Fixed releases of nixpkgs. Useful for avoiding known incompatibilities.
    nixpkgs-2016-03 nixpkgs-2016-09

    # Default nixpkgs, overridden with helper functions and packages
    nix-config;

  # Regular dependencies, used as-is
  inherit (self.nixpkgs)
    cabal-install;

  # Fixed versions to avoid known breakages
  inherit (self.nixpkgs-2016-03)
    # Args differ in new versions, which breaks ./nix-support/haskellPackages.nix scripts
    cabal2nix;

  inherit (self.nixpkgs-2016-09)
    # The quoting is different in other versions, which breaks e.g. wrap
    makeWrapper

    # Old versions don't have the needed contracts, new ones don't build on i686
    racket;

  # Helper functions, etc.
  inherit (self.helpers)
    allDrvsIn attrsToDirs backtrace fail inNixedDir isBroken latestGit mkBin
    nixListToBashArray nixpkgs1803 nothing pipeToNix reverse sanitiseName
    stripOverrides tryElse unlines unpack withDeps wrap;

  inherit (self.warbo-packages)
    asv timeout;

  # Cases where we want both the attribute set and its attributes available
  inherit (self.callPackage ./nix-support/annotate.nix {})
    annotated annotateRawAstsFrom;

  inherit (self.dumpToNixScripts)
    dumpToNix;

  inherit (self.runTypesScriptData)
    runTypesScript;

  # We take Nix from the system. This is impure, but unavoidable since different
  # Nix versions will behave differently anyway (e.g. when using 'withNix')
  inherit (import self.tePath {}) nix;

  # A bug in nixpkgs 18.03 seems to prevent libuv building on i686. We can use
  # pre-built packages from a binary cache (which were presumably cross-compiled
  # on x86-64 machines).
  # This is a pretty core library, which makes this project unusable on that
  # OS+CPU combo; which, notably, is what the author uses for development...
  # To mitigate this we check if that OS+CPU is in use, and if so we replace
  # some pinned packages which are known to be broken with packages taken
  # impurely from the running system. Note that Nix is such a package, but it's
  # always taken from the running system anyway (see above).
  inherit (with rec {
            versionFile = self.path + "/.version";
            version     = if pathExists versionFile
                             then replaceStrings [ "\n" "" ] [ "" "" ]
                                                 (readFile versionFile)
                             else "0";
            libuvBug    = currentSystem == "i686-linux" && version == "18.03";
            warn        = ''
              WARNING: Detected nixpkgs 18.03 on i686. This has a known
              problem with libuv, so we're taking the 'jq' package from
              <nixpkgs> instead of using the pinned version. Hopefully
              the system's version isn't broken too...
            '';
          };
          if libuvBug
             then trace warn import self.tePath {}
             else super)
    jq;

  analysis              = self.callPackage ./nix-support/analysis.nix              {};
  asv-nix               = self.callPackage ./nix-support/asv-nix.nix               {};
  buckets               = self.callPackage ./nix-support/buckets.nix               {};
  callHackage           = self.callPackage ./nix-support/callHackage.nix           {};
  checkHsEnv            = self.callPackage ./nix-support/checkHsEnv.nix            {};
  checkStderr           = self.callPackage ./nix-support/checkStderr.nix           {};
  cluster               = self.callPackage ./nix-support/cluster.nix               {};
  concurrentQuickspec   = self.callPackage ./nix-support/concurrentQuickspec.nix   {};
  dumpToNixScripts      = self.callPackage ./nix-support/dumpToNix.nix             {};
  extractedEnv          = self.callPackage ./nix-support/extractedEnv.nix          {};
  extraHaskellPackages  = self.callPackage ./nix-support/extraHaskellPackages.nix  {};
  filterToSampled       = self.callPackage ./nix-support/filterToSampled.nix       {};
  format                = self.callPackage ./nix-support/format.nix                {};
  genQuickspecRunner    = self.callPackage ./nix-support/genQuickspecRunner.nix    {};
  getDepsScript         = self.callPackage ./nix-support/getDepsScript.nix         {};
  haskellPackages       = import ./nix-support/haskellPackages.nix
                            { inherit (self) hsOverride nixpkgs; };
  haskellPkgNameVersion = self.callPackage ./nix-support/haskellPkgNameVersion.nix {};
  haskellPkgToAsts      = self.callPackage ./nix-support/haskellPkgToAsts.nix      {};
  haskellPkgToRawAsts   = self.callPackage ./nix-support/haskellPkgToRawAsts.nix   {};
  haveVar               = self.callPackage ./nix-support/haveVar.nix               {};
  hsNameVersion         = self.callPackage ./nix-support/hsNameVersion.nix         {};
  hsOverride            = self.callPackage ./nix-support/hsOverride.nix            {};
  makeHaskellPkgNixable = self.callPackage ./nix-support/makeHaskellPkgNixable.nix {};
  ML4HSFE               = self.callPackage ./nix-support/ML4HSFE.nix               {};
  nixedHsPkg            = self.callPackage ./nix-support/nixedHsPkg.nix            {};
  nixEnv                = import ./nix-support/nixEnv.nix { inherit (self) withNix; };
  package               = self.callPackage ./nix-support/package.nix               {};
  pkgName               = self.callPackage ./nix-support/pkgName.nix               {};
  quickspec             = self.callPackage ./nix-support/quickspec.nix             {};
  quickspecAsts         = self.callPackage ./nix-support/quickspecAsts.nix         {};
  reduce-equations      = self.callPackage ./nix-support/reduce-equations.nix      {};
  renderEqs             = self.callPackage ./nix-support/renderEqs.nix             {};
  runTypesScriptData    = self.callPackage ./nix-support/runTypesScript.nix        {};
  runWeka               = self.callPackage ./nix-support/runWeka.nix               {};
  stableHackageDb       = self.callPackage ./nix-support/stableHackageDb.nix       {};
  testData              = self.callPackage ./nix-support/testData.nix              {};
  tipBenchmarks         = self.callPackage ./nix-support/tipBenchmarks.nix         {};
  tipToHaskellPkg       = self.callPackage ./nix-support/tipToHaskellPkg.nix       {};
  tryTip                = self.callPackage ./nix-support/tryTip.nix                {};
  warbo-packages        = self.callPackage ./nix-support/warbo-packages.nix        {};
  withNix               = self.callPackage ./nix-support/withNix.nix               {};

  # Used for general performance testing, as well as formal evaluation
  benchmarkEnv    = import ./benchmarkEnv.nix;
  benchmarkRunner = import ./benchmarks { inherit (self) pkgs; };
}
