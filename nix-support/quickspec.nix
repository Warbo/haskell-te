{ bash, fail, haskellPkgToAsts, jq, lib, makeHaskellPkgNixable, mkBin, nixEnv,
  quickspecAsts, runCommand, testData, unpack, withDeps, writeScript }:

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

      [[ "$#" -gt 0 ]] || fail 'quickspec: No Haskell dirs given as args'

      DIRS=()
      for D in "$@"
      do
        D_ARG=$(readlink -f "$D")
        [[ -d "$D_ARG" ]] || fail "quickspec arg '$D' isn't dir (or link)"

        DIR=$(makeHaskellPkgNixable "$D_ARG") || fail "Couldn't nixify '$D'"
        DIRS+=($DIR)
      done

      function getAsts {
        for DIR in "''${DIRS[@]}"
        do
          haskellPkgToAsts "$DIR"
        done | jq -s 'reduce .[] as $x ([]; . + $x)'
      }

      getAsts | quickspecAsts "''${DIRS[@]}"
    '';
  };

  testGarbage = runCommand "check-garbage"
    {
      buildInputs  = [ fail quickspec ];
      IN_SELF_TEST = "1";
    }
    ''
      if echo '!"£$%^&*()' | quickspec 1> /dev/null 2> garbage.err
      then
        cat garbage.err 1>&2
        fail "Shouldn't have accepted garbage"
      fi
      echo "pass" > "$out"
    '';

  testMultiple = runCommand "quickcheck-multiple"
    {
      plus  = testData.commands.haskellPkg {
        name = "plus";
        tip  = writeScript "plus.smt2" ''
          (declare-datatypes () ((Nat (Z) (S (p Nat)))))

          (define-fun succ ((n Nat)) Nat
            (as (S n) Nat))

          (define-fun-rec plus ((x Nat) (y Nat)) Nat
             (match x
               (case  Z      y)
               (case (S x2) (S (plus x2 y)))))

          (check-sat)
        '';
      };
      loop = testData.commands.haskellPkg {
        name = "loop";
        tip  = writeScript "loop.smt2" ''
          (declare-datatypes () ((Nat (Z) (S (p Nat)))))

          (define-fun-rec
            (par (a)
              (loop ((f (=> a a)) (x a) (n Nat)) a
                (match n
                  (case  Z     x)
                  (case (S m) (loop f (@ f x) m))))))

          (check-sat)
        '';
      };
      buildInputs  = [ fail jq quickspec ];
      IN_SELF_TEST = "1";
      CHECK = ''
        . as $in | [paths(type == "object" and has("symbol"))]          |
                   map(. as $p | $in | getpath($p) | .symbol | . == $f) |
                   any
      '';
    }
    ''
      set -e

      echo "Patching loop pkg to avoid conflicting with plus pkg" 1>&2
      cp -r "$loop" ./loop
      chmod +w -R   ./loop

      mv  ./loop/src/A.hs                  ./loop/src/Loop.hs
      sed -e 's/module A/module Loop/g' -i ./loop/src/Loop.hs


      mv ./loop/tip-benchmark-sig.cabal                        ./loop/loop.cabal
      sed -e 's/tip-benchmark-sig/loop-pkg/g'               -i ./loop/loop.cabal
      sed -e 's/exposed-modules:.*/exposed-modules: Loop/g' -i ./loop/loop.cabal

      echo "Exploring..." 1>&2
      EQS=$(quickspec "$plus" ./loop)

      echo "Checking expression" 1>&2
      echo "$EQS" | jq -e --arg f "shouldNotExist" "$CHECK | not"

      for F in plus loop
      do
        echo "Checking for equations with $F" 1>&2
        echo "$EQS" | jq -e --arg f "$F" "$CHECK"
      done
      mkdir "$out"
    '';

  checks = [ testGarbage testMultiple ] ++ attrValues testHsPkgs;

  testHsPkgs =
    mapAttrs (n: eqs: runCommand "test-quickspec-${n}"
                        {
                          inherit eqs;
                          buildInputs = [ fail jq ];
                        }
                        ''
                          set -e
                          RESULTS=$(jq 'length' < "$eqs") ||
                            fail "Couldn't get equation array"

                          [[ "$RESULTS" -gt 0 ]] ||
                            fail "Found no equations $eqs"
                          mkdir "$out"
                        '')
             (testData.finalEqs { script = quickspec; });
};

withDeps checks quickspec
