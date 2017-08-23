{ attrsToDirs, bash, fail, haskellPkgToAsts, jq, makeHaskellPkgNixable,
  quickspecAsts, runCommand, tipToHaskellPkg, withDeps, wrap }:

with rec {
  quickspec = attrsToDirs {
    bin = {
      quickspec = wrap {
        name  = "quickspec";
        paths = [
          bash haskellPkgToAsts jq makeHaskellPkgNixable quickspecAsts
        ];
        vars   = {};
        script = ''
          #!/usr/bin/env bash
          set -e
          set -o pipefail

          [[ -n "$1" ]] || fail "quickspec needs a dir as argument"
          [[ -d "$1" ]] || fail "quickspec arg '$1' isn't a directory"

          DIR=$(makeHaskellPkgNixable "$1") || fail "Couldn't nixify '$1'"
          haskellPkgToAsts "$DIR" | quickspecAsts "$DIR"
        '';
      };
    };
  };

  test = name: code: runCommand "quickspec-${name}-test"
    {
      given       = name;
      buildInputs = [ fail jq quickspec tipToHaskellPkg ];
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

    (test "can-run-quickspec" ''
      PKG=$(tipToHaskellPkg < "${../tests/example.smt2}")
      BENCH_OUT=$(quickspec "$PKG") ||
        fail "Failed to run.\n$BENCH_OUT"

      RESULTS=$(echo "$BENCH_OUT" | jq 'length') ||
        fail "Couldn't get equation array"

      [[ "$RESULTS" -gt 0 ]] || fail "Found no equations $BENCH_OUT"
    '')
  ];
};

withDeps checks quickspec
