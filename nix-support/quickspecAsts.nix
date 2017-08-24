{ attrsToDirs, bash, checkStderr, fail, glibcLocales, haskellPackages,
  haskellPkgNameVersion, jq, lib, makeHaskellPkgNixable, nix, nixEnv,
  quickspecBench, runCommand, testData, timeout, withDeps, wrap }:

with lib;
with { inherit (quickspecBench) getCmd innerNixPath mkPkgInner; };
with rec {
  genSig2 = wrap {
    name   = "gen-sig2";
    paths  = [
      fail nix (haskellPackages.ghcWithPackages (h: [ h.mlspec h.nix-eval ]))
    ];
    vars   = nixEnv // {
      inherit getCmd;
      NIX_EVAL_HASKELL_PKGS = toString ./quickspecEnv.nix;
      #NIX_PATH              = innerNixPath;
    };
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

      ALL=$(cat)
       QS=$(echo "$ALL" | jq 'map(select(.quickspecable))')

      { echo "$QS" | runhaskell "$getCmd"; } || {
        echo -e "Given:\n$ALL\n" 1>&2
        echo -e "Chosen:\n$QS\n" 1>&2
        fail "Couldn't generate QuickSpec code"
      }
    '';
  };

  quickspecAsts = attrsToDirs {
    bin = {
      quickspecAsts = wrap {
        name  = "quickspecAsts";
        paths = [ bash haskellPkgNameVersion jq makeHaskellPkgNixable nix
                  timeout ];
        vars  = nixEnv // {
          inherit checkStderr genSig2 mkPkgInner;
          LANG                  = "en_US.UTF-8";
          LOCALE_ARCHIVE        = "${glibcLocales}/lib/locale/locale-archive";
          NIX_EVAL_HASKELL_PKGS = toString ./quickspecEnv.nix;
        };
        script = ''
          #!/usr/bin/env bash
          set   -e
          set   -o pipefail
          shopt -s nullglob

          DIR=$(makeHaskellPkgNixable "$1")
          export DIR

          PKG_NAME=$(haskellPkgNameVersion "$DIR" | jq -r '.package')
          export PKG_NAME

          OUTPUT=$("$genSig2")

          HASKELL_PROGRAM_CODE=$(echo "$OUTPUT" | jq -r '.code'  )
                        NIXENV=$(echo "$OUTPUT" | jq -r '.env'   )
                           CMD=$(echo "$OUTPUT" | jq -r '.runner')

          function run() {
            withTimeout nix-shell -p "$NIXENV" --run "$CMD"
          }

          function keepJson() {
            # Strip out cruft that QuickSpec puts on stdout. Since this is just a
            # filter, we don't actually care if grep finds anything or not; hence
            # we use '|| true' to avoid signalling an error, and hide this
            # complexity inside a function.
            grep -v '^Depth' || true
          }

          echo "$HASKELL_PROGRAM_CODE" | run 2> >("$checkStderr") |
                                         keepJson                 |
                                         jq -s '.'
        '';
      };
    };
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

  testAsts = mapAttrs
    (n: asts: runCommand "test-quickspecasts-${n}"
      {
        inherit asts;
        allowFail   = if elem n [ "nat-full" "teBenchmark" ]
                         then "true"
                         else "false";
        buildInputs = [ fail jq quickspecAsts ];
        pkg         = getAttr n testData.haskellPkgs;
        MAX_SECS    = "180";
        MAX_KB      = "1000000";
        FAIL_MSG    = ''
          quickspecAsts failed, but this theory is known to be problematic (e.g.
          running out of time or memory). Storing stderr in our output to aid in
          debugging if it turns out to be a different problem.
        '';
      }
      ''
        BENCH_OUT=$(quickspecAsts "$pkg" < "$asts" 2> >(tee stderr 1>&2)) || {
          if "$allowFail"
          then
            echo "$FAIL_MSG" 1>&2
            mkdir -p "$out"
            cp stderr "$out"/
            exit 0
          else
            fail "Failed to run $n.\n$BENCH_OUT"
          fi
        }

        RESULTS=$(echo "$BENCH_OUT" | jq 'length') ||
          fail "Couldn't get equation array for $n"

        [[ "$RESULTS" -gt 0 ]] || fail "No equations for $n: $BENCH_OUT"

        echo "pass" > "$out"
    '')
    testData.asts;

  checks = [ testGarbage ] ++ attrValues testAsts;
};

withDeps checks quickspecAsts
