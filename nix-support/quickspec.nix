{ attrsToDirs, bash, checkStderr, fail, glibcLocales, jq, nix, nixEnv,
  pipeToNix, quickspecBench, runCommand, withDeps, wrap }:

with { inherit (quickspecBench) customHs genSig2 getInput mkPkgInner setUpDir; };
with rec {
  quickspec = attrsToDirs {
    bin = {
      quickspec = wrap {
        name  = "quickspec";
        paths = [ bash jq nix pipeToNix ];
        vars  = nixEnv // {
          inherit checkStderr genSig2 mkPkgInner;
          LANG                  = "en_US.UTF-8";
          LOCALE_ARCHIVE        = "${glibcLocales}/lib/locale/locale-archive";
          NIX_EVAL_HASKELL_PKGS = customHs;
        };
        script = ''
          #!/usr/bin/env bash
          set -e

          ${setUpDir}
          ${getInput}

          OUTPUT=$("$genSig2" < "$ANNOTATED")

          HASKELL_PROGRAM_CODE=$(echo "$OUTPUT" | jq -r '.code'  )
                        NIXENV=$(echo "$OUTPUT" | jq -r '.env'   )
                           CMD=$(echo "$OUTPUT" | jq -r '.runner')

          function run() {
            if [[ -n "$NIXENV" ]]
            then
              nix-shell -p "$NIXENV" --run "$CMD"
            else
              $CMD "$HASKELL_PROGRAM_CODE"
            fi
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

  test = name: code: runCommand "quickspec-${name}-test"
    {
      given       = name;
      buildInputs = [ fail jq pipeToNix quickspec ];
    }
    ''
      #!/usr/bin/env bash
      set -e
      {
        ${code}
      } || exit 1
      echo "pass" > "$out"
    '';

  checks = [
    (test "check-garbage" ''
      if echo '!"£$%^&*()' | quickspec 1> /dev/null 2> garbage.err
      then
        cat garbage.err 1>&2
        fail "Shouldn't have accepted garbage"
      fi
    '')

    (test "can-run-quickspecbench" ''
      BENCH_OUT=$(quickspec < "${../tests/example.smt2}" | pipeToNix) ||
        fail "Failed to run.\n$BENCH_OUT"

      echo "Cached to $BENCH_OUT" 1>&2

      RESULTS=$(jq 'length' < "$BENCH_OUT") ||
        fail "Couldn't get equation array"

      [[ "$RESULTS" -gt 0 ]] || fail "Found no equations"
    '')
  ];
};

withDeps checks quickspec
