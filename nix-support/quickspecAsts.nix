{ analysis, annotated, bash, fail, genQuickspecRunner, glibcLocales,
  jq, lib, makeHaskellPkgNixable, mkBin, runCommand, testData, unpack,
  withDeps, withNix }:

with lib;
with rec {
  quickspecAsts = mkBin {
    name  = "quickspecAsts";
    paths = [ bash genQuickspecRunner jq makeHaskellPkgNixable ];
    vars  = {
      LANG                  = "en_US.UTF-8";
      LOCALE_ARCHIVE        = "${glibcLocales}/lib/locale/locale-archive";
      NIX_EVAL_HASKELL_PKGS = builtins.toString ./quickspecEnv.nix;
    };
    script = ''
      #!/usr/bin/env bash
      set   -e
      set   -o pipefail

      function mkNixable {
        for P in "$@"
        do
          makeHaskellPkgNixable "$P" | jq -R '.'
        done
      }

      OUT_DIRS=$(mkNixable "$@" | jq -s '.')
      export OUT_DIRS

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
    {
      buildInputs  = [ analysis fail jq ];
      eqs          = eqss.test-theory;
      GROUND_TRUTH = testData.truth.test-theory;
      TRUTH_SOURCE = testData.truth.test-theory;
    }
    ''
      set -e
      set -o pipefail
      RESULT=$(precision_recall_eqs < "$eqs")
      RECALL=$(echo "$RESULT" | jq '.recall') || fail "No recall"
      echo "$RECALL" | jq -e '. > 0' || fail "Recall is '$RECALL'"
      mkdir "$out"
    '';

  checks = attrValues testAsts                  ++
           attrValues (mapAttrs moreTests eqss) ++
           [ checkParamTypes testGarbage ];
};

withDeps checks quickspecAsts
