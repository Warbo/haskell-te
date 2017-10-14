{ annotated, bash, fail, genQuickspecRunner, glibcLocales,
  haskellPkgNameVersion, jq, lib, makeHaskellPkgNixable, mkBin, nixedHsPkg,
  nixEnv, runCommand, testData, tipBenchmarks, unpack, withDeps, withNix }:

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

  eqss = testData.eqs { script = quickspecAsts; };

  testAsts = mapAttrs
    (n: eqs: runCommand "test-quickspecasts-${n}"
      {
        inherit eqs n;
        buildInputs = [ fail jq ];
      }
      ''
        set -e
        RESULTS=$(jq 'length' < "$eqs") ||
          fail "Couldn't get equation array for $n"

        [[ "$RESULTS" -gt 0 ]] || fail "No equations for $n: $eqs"
        mkdir "$out"
    '')
    eqss;

  moreTests = attr: eqs:
    with rec {
      pkg     = getAttr attr testData.haskellDrvs;
      name    = pkg.name;
      haveEqs = runCommand "haveEquations-${name}"
        {
          inherit eqs;
          buildInputs = [ jq ];
        }
        ''
          set -e
          jq -e 'type == "array"'            < "$eqs"
          jq -e 'map(has("relation")) | all' < "$eqs"
          mkdir "$out"
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

  checkParamTypes = runCommand "can-find-properties-of-parameterised-types"
    (withNix {
      buildInputs  = [ fail jq tipBenchmarks.tools ];
      eqs          = eqss.test-theory;
      GROUND_TRUTH = ../tests/test-theory-truth.smt2;
      TRUTH_SOURCE = ../tests/test-theory-truth.smt2;
    })
    ''
      set -e
      set -o pipefail
      RESULT=$(echo "$eqs" | precision_recall_eqs)
               echo "$RESULT" | jq -e '.recall | . > 0' || fail "No recall"
      mkdir "$out"
    '';

  checks = attrValues testAsts                  ++
           attrValues (mapAttrs moreTests eqss) ++
           [ checkParamTypes testGarbage ];
};

withDeps checks quickspecAsts
