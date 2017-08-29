# Custom definitions, mixed in with inherited utility packages
args:

# Fetch known revisions of nixpkgs, so we're not at the mercy of system updates
with rec {
  inherit (import ./nixpkgs.nix) mkNixpkgs-2016-03 mkNixpkgs-2016-09;
  defaultNixpkgs  = mkNixpkgs-2016-03;
  nixpkgs         = defaultNixpkgs args;
  nixpkgs-2016-03 = mkNixpkgs-2016-03 args;
  nixpkgs-2016-09 = mkNixpkgs-2016-09 args;
};

# We define things in stages, to avoid everything depending on everything else

# Built-in nixpkgs stuff, used as-is

with builtins; with nixpkgs.lib;

with { inherit (nixpkgs) buildEnv jq runCommand writeScript; };

# External dependencies, and the helpers needed to load them

with {
  inherit (nixpkgs.callPackage ./nixFromCabal.nix {})
    nixFromCabal nixedHsPkg;

  inherit (nixpkgs.callPackage ./nix-config.nix {
            mkNixpkgs = mkNixpkgs-2016-09;
          })
    nix-config nix-config-src;
};

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

  havePath = n: any (x: x.prefix == n) nixPath;
};

with (nixpkgs.callPackage ./haskellPackages.nix {
       inherit extractTarball havePath nix-config nixFromCabal;
       callHackage          = nixpkgs.callPackage ./callHackage.nix {};
       superHaskellPackages = nixpkgs.haskellPackages;
     });

# Inherit from the result, so that haskellPackages.override works on the
# available packages, rather than the arguments to this callPackage invocation

let pkgs = rec {
  # Include the above definitions
  inherit drvFromScript extractTarball haskellPackages hsOverride nixedHsPkg
          nixEnv nix-config nix-config-src nixFromCabal nixpkgs-2016-09 withNix;

  inherit (nixpkgs-2016-09)
    # Use newer makeWrapper for quoting changes
    makeWrapper

    # Use newer Racket for contract definitions
    racket;

  # Useful for setting dependencies, variables, etc. of scripts
  inherit (nix-config)
    attrsToDirs inNixedDir nixListToBashArray stripOverrides timeout unpack
    withDeps wrap;

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
  backtrace             = callPackage ./backtrace.nix             {};
  bashEscape            = callPackage ./bashEscape.nix            {};
  benchmarkEnv          = callPackage ./benchmarkEnv.nix          {};
  buckets               = callPackage ./buckets.nix               {};
  cacheContent          = callPackage ./cacheContent.nix          {};
  cluster               = callPackage ./cluster.nix               {};
  dumpPackage           = callPackage ./dumpPackage.nix           {};
  explore               = callPackage ./explore.nix               {};
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
  mkBin                 = callPackage ./mkBin.nix                 {};
  mlspecBench           = callPackage ./mlspecBench.nix           {};
  package               = callPackage ./package.nix               {};
  parseJSON             = callPackage ./parseJSON.nix             {};
  pkgName               = callPackage ./pkgName.nix               {};
  quickspec             = callPackage ./quickspec.nix             {};
  quickspecAsts         = callPackage ./quickspecAsts.nix         {};
  quickspecBench        = callPackage ./quickspecBench.nix        {};
  runScript             = callPackage ./runScript.nix             {};
  runTypes              = callPackage ./runTypes.nix              {};
  sta                   = callPackage ./sta.nix                   {};
  testData              = callPackage ./testData.nix              {};
  tipToHaskellPkg       = callPackage ./tipToHaskellPkg.nix       {};

  buildPackage  = callPackage ./buildPackage.nix
                    { inherit (haskellPackages) cabal2nix cabal-install; };
  downloadToNix = callPackage ./downloadToNix.nix
                    { inherit (haskellPackages) cabal-install;           };
  getDepsScript = callPackage ./getDepsScript.nix
                    { inherit (haskellPackages) GetDeps;                 };
  tests         = callPackage ./tests.nix
                    { pkgs = nixpkgs // pkgs;                            };

  tipBenchmarks = callPackage ./tipBenchmarks.nix  {
    pkgs = nixpkgs-2016-09;
  };

  annotate = annotateScripts.annotate;

  annotated = pkgDir: annotate rec {
    pkg    = { name = "dummy"; };
    asts   = dumpToNix { pkgDir = pkgSrc; };
    pkgSrc = nixedHsPkg pkgDir;
  };

  annotateScripts = callPackage ./annotate.nix {};

  callPackage = nixpkgs.newScope pkgs;

  checkFailures = type: results:
    assert type == "any" || type == "all";
    let names = attrNames results;
        fails = let l = concatMap (n: if isList results."${n}"
                                         then results."${n}"
                                         else [ results."${n}" ]) names;
                 in map (x: x.failed) l;
        bFunc = if type == "any" then any else all;
     in if all isBool fails
           then bFunc id fails
           else drvFromScript { inherit type; inherit fails; } ''
                  for FAIL in $fails
                  do
                    cat "$FAIL"
                  done | grep '^.' | jq -s '. | ${type}' > "$out"
                '';

  # Use 'dbug foo bar' in place of 'bar' when 'bar' is fragile, tricky, etc. The
  # value of 'foo' will be included in the stack trace in case of an error, and
  # if the environment variable "TRACE" is non-empty it will also be printed out
  # when there's no error
  dbug = info: val:
    let msg = toJSON { inherit info; };
        v   = if getEnv "TRACE" == ""
                 then val
                 else trace info val;
     in addErrorContext msg v;

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

  fail = mkBin {
    name   = "fail";
    paths  = [ nixpkgs.bash backtrace ];
    script = ''
      #!/usr/bin/env bash
      set -e
      echo -e "$*" 1>&2
      {
        echo "Backtrace:"
        backtrace
        echo "End Backtrace"
      } 1>&2
      exit 1
    '';
  };

  haskellPackageNames = writeScript
                          "haskell-names"
                          (concatStringsSep "\n" (attrNames haskellPackages));

  pipeToNix = mkBin {
    name   = "pipeToNix";
    paths  = [ nix-config.pipeToNix ];
    script = ''
      #!/usr/bin/env bash
      X=$(pipeToNix "$@")
      echo "Cached data to $X" 1>&2
      echo "$X"
    '';
  };

  runTypesScriptData = callPackage ./runTypesScript.nix {};
  runTypesScript     = runTypesScriptData.runTypesScript;

  runWeka = callPackage ./runWeka.nix { inherit havePath; };

  # Strips non-alphanumeric characters from a string; e.g. for use in a name
  sanitise = stringAsChars (c: if elem c (upperChars ++
                                          lowerChars ++
                                          stringToCharacters "0123456789")
                                  then c
                                  else "");

  stdParts = [ "failed" "out" "stderr" "stdout" ];

  storeParts = ''
    function fail {
      echo "$1" 1>&2
      exit 1
    }

    [[ -n "$O" ]] || fail "storeParts failed: No data given"
    echo "$O" > "$out"

    SO=$(echo "$O" | jq -r ".stdout") || fail "Failed to get .stdout"
    cp "$SO" "$stdout"

    SE=$(echo "$O" | jq -r ".stderr") || fail "Failed to get .stderr"
    cp "$SE" "$stderr"

    echo "$O" | jq -r ".failed" > "$failed" || fail "Failed to get .failed"
  '';

  storeResult = writeScript "store-result" ''
    set -e
    RESULT=$(nix-store --add "$1")
    printf '%s' "$RESULT" > "$out"
  '';

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
