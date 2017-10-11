{ bash, fail, haskellPkgToAsts, jq, lib, makeHaskellPkgNixable, mkBin, nixEnv,
  quickspecAsts, runCommand, testData, tipToHaskellPkg, withDeps }:

with lib;
with rec {
  quickspec = mkBin {
    name   = "quickspec";
    paths  = [ bash fail (haskellPkgToAsts {}) jq makeHaskellPkgNixable
               quickspecAsts ];
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

      [[ -n "$1" ]] || fail "quickspec needs a dir as argument"
      D_ARG=$(readlink -f "$1")
      [[ -d "$D_ARG" ]] || fail "quickspec arg '$1' isn't a directory (or link)"

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

  # Avoid packages which are known to timeout, get out-of-memory, etc.
  knownGoodPkgs = filterAttrs (n: _: !(elem n [ "nat-full" "teBenchmark" ]))
                              (testData.haskellPkgs {});

  testHsPkgs = mapAttrs
    (n: pkg: runCommand "test-quickspec-${n}"
      (nixEnv // {
        inherit pkg;
        buildInputs = [ fail jq quickspec ];
        MAX_SECS    = "180";
        MAX_KB      = "3000000";
      })
      ''
        BENCH_OUT=$(quickspec "$pkg" 2> >(tee stderr 1>&2)) ||
          fail "Failed to run.\n$BENCH_OUT"

        RESULTS=$(echo "$BENCH_OUT" | jq 'length') ||
          fail "Couldn't get equation array"

        [[ "$RESULTS" -gt 0 ]] || fail "Found no equations $BENCH_OUT"

        echo "pass" > "$out"
      '')
    knownGoodPkgs;
};

withDeps checks quickspec
