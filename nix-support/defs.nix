# Custom definitions, mixed in with inherited utility packages
args:

# Fetch known revisions of nixpkgs, so our 'stable' configuration isn't at the
# mercy of system updates
with { stable = args.stable or true; };
with import ./nixpkgs.nix args;

# We define things in stages, to avoid everything depending on everything else

# Built-in nixpkgs stuff, used as-is
with builtins // nixpkgs.lib // {
  inherit (nixpkgs) buildEnv jq runCommand writeScript;
  inherit (nixpkgs-2016-03) cabal2nix;
};

# External dependencies, and the helpers needed to load them

with nixpkgs.callPackage ./nixFromCabal.nix { inherit cabal2nix; };
with rec {
  nixEnv  = (nixpkgs.callPackage ./nixEnv.nix {}) null;

  withNix = nixpkgs.callPackage ./withNix.nix {
    inherit nixEnv;
  };

  drvFromScript = nixpkgs.callPackage ./drvFromScript.nix  {
    inherit withNix;
  };

  extractTarball = nixpkgs.callPackage ./extractTarball.nix {
    inherit drvFromScript;
  };
};

with (nixpkgs.callPackage ./haskellPackages.nix {
       inherit extractTarball nix-config nixFromCabal stable;
       callHackage          = nixpkgs.callPackage ./callHackage.nix {};
       superHaskellPackages = nixpkgs.haskellPackages;
     });

# Inherit from the result, so that haskellPackages.override works on the
# available packages, rather than the arguments to this callPackage invocation

let pkgs = rec {
  # Include the above definitions
  inherit cabal2nix drvFromScript extractTarball haskellPackages hsOverride
          nixedHsPkg nixEnv nix-config nix-config-src nixFromCabal
          nixpkgs-2016-09 nixpkgs-src stable withNix;

  inherit (nixpkgs-2016-09)
    # Use newer makeWrapper for quoting changes
    makeWrapper

    # Use newer Racket for contract definitions
    racket;

  # Useful for setting dependencies, variables, etc. of scripts
  inherit (nix-config)
    attrsToDirs backtrace fail inNixedDir mkBin nixListToBashArray pipeToNix
    reverse sanitiseName stripOverrides timeout unpack withDeps wrap;

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

  annotate = annotateScripts.annotate;

  annotated = pkgDir: annotate rec {
    pkg    = { name = "dummy"; };
    asts   = dumpToNix { pkgDir = pkgSrc; };
    pkgSrc = nixedHsPkg pkgDir;
  };

  callPackage    = nixpkgs.newScope pkgs;
  dumpToNix      = dumpToNixScripts.dumpToNix;
  runTypesScript = runTypesScriptData.runTypesScript;

  tests     = callPackage ./tests.nix { pkgs = nixpkgs // pkgs;  };

  testSuite = runCommand "haskell-te-tests"
                { deps = collect isDerivation tests; }
                ''echo "true" > "$out"'';

  unlines = concatStringsSep "\n";
};

in nixpkgs // pkgs
