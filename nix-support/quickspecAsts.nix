{ bash, fail, genQuickspecRunner, glibcLocales, haskellPkgNameVersion, jq, lib,
  makeHaskellPkgNixable, mkBin, nixEnv, runCommand, testData, withDeps }:

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
        inherit asts;
        buildInputs = [ fail jq quickspecAsts ];
        pkg         = getAttr n testData.haskellPkgs;
        MAX_SECS    = "180";
        MAX_KB      = "1000000";
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

  checks = [ testGarbage ] ++ attrValues testAsts;
};

withDeps checks quickspecAsts
