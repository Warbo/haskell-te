{ bash, fail, haskellPkgToAsts, jq, lib, makeHaskellPkgNixable, mkBin, nixEnv,
  quickspecAsts, runCommand, testData, tipToHaskellPkg, withDeps }:

with lib;
with rec {
  quickspec = mkBin {
    name   = "quickspec";
    paths  = [ bash haskellPkgToAsts jq makeHaskellPkgNixable quickspecAsts ];
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

  testGarbage = runCommand "check-garbage"
    {
      buildInputs = [ fail quickspec ];
    }
    ''
      if echo '!"£$%^&*()' | quickspec 1> /dev/null 2> garbage.err
      then
        cat garbage.err 1>&2
        fail "Shouldn't have accepted garbage"
      fi
      echo "pass" > "$out"
    '';

  checks = [ testGarbage ] ++ attrValues testHsPkgs;

  testHsPkgs = mapAttrs
    (n: pkg: runCommand "test-quickspec-${n}"
      (nixEnv // {
        inherit pkg;
        allowFail   = if elem n [ "nat-full" "teBenchmark" ]
                         then "true"
                         else "false";
        buildInputs = [ fail jq quickspec ];
        MAX_SECS    = "300";
        MAX_KB      = "1000000";
        FAIL_MSG    = ''
          quickspec failed, but this theory is known to be problematic (e.g.
          running out of time or memory). Storing stderr in our output to aid in
          debugging if it turns out to be a different problem.
        '';
      })
      ''
        BENCH_OUT=$(quickspec "$pkg" 2> >(tee stderr 1>&2)) || {
          if "$allowFail"
          then
            echo "$FAIL_MSG" 1>&2
            mkdir -p "$out"
            cp stderr "$out"/
            exit 0
          else
            fail "Failed to run.\n$BENCH_OUT"
          fi
        }

        RESULTS=$(echo "$BENCH_OUT" | jq 'length') ||
          fail "Couldn't get equation array"

        [[ "$RESULTS" -gt 0 ]] || fail "Found no equations $BENCH_OUT"

        echo "pass" > "$out"
      '')
    testData.haskellPkgs;
};

withDeps checks quickspec
