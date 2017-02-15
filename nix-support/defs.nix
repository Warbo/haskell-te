# Custom definitions, mixed in with inherited utility packages
args:

# Fetch known revisions of nixpkgs, so we're not at the mercy of system updates
with rec {
  inherit (import ./nixpkgs.nix args) nixpkgs-2016-03 nixpkgs-2016-09;
  nixpkgs = nixpkgs-2016-03;
};

# We define things in stages, to avoid everything depending on everything else

# Built-in nixpkgs stuff, used as-is

with builtins; with nixpkgs.lib;

with { inherit (nixpkgs) writeScript; };

# External dependencies, and the helpers needed to load them

with {
  inherit (nixpkgs.callPackage ./nixFromCabal.nix {})
    nixFromCabal nixedHsPkg;
};

with rec {
  nixEnv         = nixpkgs.callPackage ./nixEnv.nix         {};
  withNix        = nixpkgs.callPackage ./withNix.nix        {
    inherit nixEnv;
  };

  drvFromScript  = nixpkgs.callPackage ./drvFromScript.nix  {
    inherit withNix;
  };

  extractTarball = nixpkgs.callPackage ./extractTarball.nix {
    inherit drvFromScript;
  };

  havePath = n: any (x: x.prefix == n) nixPath;
};

with (nixpkgs.callPackage ./haskellPackages.nix {
       inherit extractTarball havePath nixFromCabal;
       callHackage          = nixpkgs.callPackage ./callHackage.nix {};
       superHaskellPackages = nixpkgs.haskellPackages;
     });

# Inherit from the result, so that haskellPackages.override works on the
# available packages, rather than the arguments to this callPackage invocation

let pkgs = rec {
  # Include the above definitions
  inherit drvFromScript extractTarball haskellPackages hsOverride nixedHsPkg
          nixEnv nixFromCabal withNix;

  # Use newer Racket for contract definitions
  inherit (nixpkgs-2016-09)
    racket;

  # These provide executables
  inherit (haskellPackages)
    AstPlugin GetDeps ML4HSFE mlspec reduce-equations;

  inherit (callPackage ./runBenchmark.nix {})
          runCmd checkHsEnv;

  inherit (callPackage ./benchmarkOutputs.nix {})
          processPackage processPackages;

  inherit (callPackage ./test-defs.nix {})
          runTestInDrv testAll testDbg testDrvString testFiles testMsg
          testPackages testRec testRun testWrap;

  annotate           = callPackage ./annotate.nix           {};
  benchmark          = callPackage ./benchmark.nix          { inherit havePath; };
  cluster            = callPackage ./cluster.nix            {};
  dumpPackage        = callPackage ./dumpPackage.nix        {};
  dumpToNix          = callPackage ./dumpToNix.nix          {};
  explore            = callPackage ./explore.nix            {};
  format             = callPackage ./format.nix             {};
  importDir          = callPackage ./importDir.nix          {};
  mlspecBench        = callPackage ./mlspecBench.nix        {};
  package            = callPackage ./package.nix            {};
  parseJSON          = callPackage ./parseJSON.nix          {};
  pkgName            = callPackage ./pkgName.nix            {};
  quickspecBench     = callPackage ./quickspecBench.nix     {};
  reduce             = callPackage ./reduce.nix             {};
  runScript          = callPackage ./runScript.nix          {};
  runTypes           = callPackage ./runTypes.nix           {};
  runTypesScript     = callPackage ./runTypesScript.nix     {};
  timeout            = callPackage ./timeout.nix            {};
  tipBenchmarks      = callPackage ./tipBenchmarks.nix      {
    pkgs = nixpkgs-2016-09;
  };
  withDeps           = callPackage ./withDeps.nix           {};

  buildPackage    = callPackage ./buildPackage.nix
                      { inherit (haskellPackages) cabal2nix cabal-install; };
  downloadToNix   = callPackage ./downloadToNix.nix
                      { inherit (haskellPackages) cabal-install;           };
  getDepsScript   = callPackage ./getDepsScript.nix
                      { inherit (haskellPackages) GetDeps;                 };
  tests           = callPackage ./tests.nix
                      { inherit pkgs;                                      };

  annotated = pkgDir:
    let nixed  = toString (nixedHsPkg pkgDir);
        dumped = dumpPackage { src = nixed; };
        ann    = annotate {
                   pkg    = { name = "dummy"; };
                   asts   = dumped.stdout;
                   pkgSrc = nixed;
                 };
        failed = drvFromScript
                   {
                     dumpF = dumped.failed;
                     dumpE = dumped.stderr;
                      annF = ann.failed;
                      annE = ann.stderr;
                   }
                   ''
                     D=$(cat "$dumpF")
                     [[ "x$D" = "xfalse" ]] || {
                       cat "$dumpE" 1>&2
                       echo "Dump failed (failed = '$D')" 1>&2
                       exit 1
                     }

                     A=$(cat "$annF")
                     [[ "x$A" = "xfalse" ]] || {
                       cat "$annE" 1>&2
                       echo "Annotate failed (failed = '$A')" 1>&2
                       exit 1
                     }
                     touch "$out"
                   '';
     in drvFromScript
          {
            inherit failed;
            ann = ann.stdout;
          }
          ''
             cp "$ann" "$out"
          '';

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

  runWeka = callPackage (if havePath "runWeka"
                            then <runWeka>
                            else ../packages/runWeka) {};

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
};

in nixpkgs // pkgs
