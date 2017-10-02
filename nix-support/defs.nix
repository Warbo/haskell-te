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
          nixpkgs-2016-09 withNix;

  inherit (nixpkgs-2016-09)
    # Use newer makeWrapper for quoting changes
    makeWrapper

    # Use newer Racket for contract definitions
    racket;

  # Useful for setting dependencies, variables, etc. of scripts
  inherit (nix-config)
    attrsToDirs backtrace fail inNixedDir mkBin nixListToBashArray pipeToNix
    reverse stripOverrides timeout unpack withDeps wrap;

  # These provide executables
  inherit (haskellPackages)
    AstPlugin GetDeps ML4HSFE mlspec reduce-equations;

  inherit (callPackage ./runBenchmark.nix {})
          runCmd checkHsEnv checkStderr;

  inherit (callPackage ./test-defs.nix {})
          runTestInDrv testAll testDbg testDrvString testFiles testMsg
          testPackages testRec testRun testWrap;

  annotateRawAstsFrom   = callPackage ./annotateRawAstsFrom.nix   {};
  asv-nix               = callPackage ./asv-nix.nix               {};
  bashEscape            = callPackage ./bashEscape.nix            {};
  benchmarkEnv          = callPackage ./benchmarkEnv.nix          {};
  buckets               = callPackage ./buckets.nix               {};
  cacheContent          = callPackage ./cacheContent.nix          {};
  cluster               = callPackage ./cluster.nix               {};
  explore               = callPackage ./explore.nix               {};
  filterToSampled       = callPackage ./filterToSampled.nix       {};
  format                = callPackage ./format.nix                {};
  genQuickspecRunner    = callPackage ./genQuickspecRunner.nix    {};
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
  runScript             = callPackage ./runScript.nix             {};
  runTypes              = callPackage ./runTypes.nix              {};
  sta                   = callPackage ./sta.nix                   {};
  testData              = callPackage ./testData.nix              {};
  tipToHaskellPkg       = callPackage ./tipToHaskellPkg.nix       {};
  tryElse               = callPackage ./tryElse.nix               {};

  getDepsScript = callPackage ./getDepsScript.nix
                    { inherit (haskellPackages) GetDeps;                 };
  tests         = callPackage ./tests.nix
                    { pkgs = nixpkgs // pkgs;                            };

  tipBenchmarks = callPackage ./tipBenchmarks.nix  {
    inherit nixpkgs-src stable;
  };

  annotate = annotateScripts.annotate;

  annotated = pkgDir: annotate rec {
    pkg    = { name = "dummy"; };
    asts   = dumpToNix { pkgDir = pkgSrc; };
    pkgSrc = nixedHsPkg pkgDir;
  };

  annotateScripts = callPackage ./annotate.nix {};

  callPackage = nixpkgs.newScope pkgs;

  defaultClusters = [ 1 2 4 ];

  dumpToNixScripts = callPackage ./dumpToNix.nix {};
  dumpToNix        = dumpToNixScripts.dumpToNix;

  ensureVars = vars: concatStringsSep "\n"
                       (map (v: ''
                                  [[ -n "${"$" + v}" ]] || {
                                    echo "Required variable '${v}' is empty" 1>&2
                                    exit 2
                                  }
                                '')
                            vars);

  haskellPackageNames = writeScript
                          "haskell-names"
                          (concatStringsSep "\n" (attrNames haskellPackages));

  runTypesScriptData = callPackage ./runTypesScript.nix {};
  runTypesScript     = runTypesScriptData.runTypesScript;

  runWeka = callPackage ./runWeka.nix { inherit stable; };

  # Strips non-alphanumeric characters from a string; e.g. for use in a name
  sanitise = stringAsChars (c: if elem c (upperChars ++
                                          lowerChars ++
                                          stringToCharacters "0123456789")
                                  then c
                                  else "");

  strip = s: let unpre = removePrefix "\n" (removePrefix " " s);
                 unsuf = removeSuffix "\n" (removeSuffix " " unpre);
              in if unsuf == s
                    then s
                    else strip unsuf;

  testSuite = runCommand "haskell-te-tests"
                { deps = collect isDerivation tests; }
                ''echo "true" > "$out"'';
};

in nixpkgs // pkgs
