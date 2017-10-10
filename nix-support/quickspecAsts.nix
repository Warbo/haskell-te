{ annotated, bash, fail, genQuickspecRunner, glibcLocales, haskellPackages,
  haskellPkgNameVersion, jq, lib, makeHaskellPkgNixable, mkBin, nixedHsPkg,
  nixEnv, runCommand, testData, testPackageNames, unpack, withDeps }:

with lib;
with rec {
  quickspecAsts = mkBin {
    name  = "quickspecAsts";
    paths = [ bash genQuickspecRunner haskellPkgNameVersion jq
              makeHaskellPkgNixable ];
    vars  = {
      LANG                  = "en_US.UTF-8";
      LOCALE_ARCHIVE        = "${glibcLocales}/lib/locale/locale-archive";
      NIX_EVAL_HASKELL_PKGS = builtins.toString ./quickspecEnv.nix;
    };
    script = ''
      #!/usr/bin/env bash
      set   -e
      set   -o pipefail

      OUT_DIR=$(makeHaskellPkgNixable "$1")
      export OUT_DIR

      PKG_NAME=$(haskellPkgNameVersion "$OUT_DIR" | jq -r '.package')
      export PKG_NAME

      S=$(genQuickspecRunner)

      [[ -e "$S" ]] || fail "Runner '$S' doesn't exist"
      "$S"
    '';
  };

  testGarbage = runCommand "check-garbage"
    {
      buildInputs = [ fail quickspecAsts ];
    }
    ''
      if echo '!"£$%^&*()' | quickspecAsts 1> /dev/null 2> garbage.err
      then
        cat garbage.err 1>&2
        fail "Shouldn't have accepted garbage"
      fi
      echo pass > "$out"
    '';

  # Avoid packages which are known to timeout, get out-of-memory, etc.
  knownGoodPkgs = filterAttrs (n: _: !(elem n [ "nat-full" "teBenchmark" ]))
                              testData.asts;

  testAsts = mapAttrs
    (n: asts: runCommand "test-quickspecasts-${n}"
      (nixEnv // {
        inherit asts n;
        buildInputs = [ fail jq quickspecAsts ];
        pkg         = getAttr n testData.haskellDrvs;
        MAX_SECS    = "180";
        MAX_KB      = "2000000";
      })
      ''
        BENCH_OUT=$(quickspecAsts "$pkg" < "$asts" 2> >(tee stderr 1>&2)) ||
          fail "Failed to run $n.\n$BENCH_OUT"

        RESULTS=$(echo "$BENCH_OUT" | jq 'length') ||
          fail "Couldn't get equation array for $n"

        [[ "$RESULTS" -gt 0 ]] || fail "No equations for $n: $BENCH_OUT"

        echo "pass" > "$out"
    '')
    knownGoodPkgs;

  moreTests = attr:
    with rec {
      pkg  = getAttr attr haskellPackages;
      name = pkg.name;
      eqs  = runCommand "eqs-of-${name}"
        {
          asts        = annotated { pkgDir = unpack pkg.src; };
          buildInputs = [ quickspecAsts ];
          OUT_DIR     = nixedHsPkg (unpack pkg.src);
        }
        ''
          set -e
          quickspecAsts < "$asts" > "$out"
        '';

      haveEqs = runCommand "haveEquations-${name}"
        {
          inherit eqs;
          buildInputs = [ jq ];
        }
        ''
          set -e
          jq -e 'type == "array"'            < "$eqs" >> "$out"
          jq -e 'map(has("relation")) | all' < "$eqs" >> "$out"
        '';

      foundEqs = runCommand "${name}-eqs-found"
        {
          inherit eqs;
          buildInputs = [ jq ];
        }
        ''
          set -e
          jq -e 'length | . > 0' < "$eqs"
          mkdir "$out"
        '';
    };
    [ foundEqs haveEqs ];

  checks = attrValues testAsts ++ map moreTests testPackageNames ++ [
    testGarbage
  ];
};

withDeps checks quickspecAsts
