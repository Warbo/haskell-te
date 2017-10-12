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

  testHsPkgs =
    mapAttrs (n: eqs: runCommand "test-quickspec-${n}"
                        {
                          inherit eqs;
                          buildInputs = [ fail jq ];
                        }
                        ''
                          set -e
                          RESULTS=$(echo "$eqs" | jq 'length') ||
                            fail "Couldn't get equation array"

                          [[ "$RESULTS" -gt 0 ]] ||
                            fail "Found no equations $eqs"
                          mkdir "$out"
                        '')
             (testData.finalEqs { script = quickspec; });
};

withDeps checks quickspec
