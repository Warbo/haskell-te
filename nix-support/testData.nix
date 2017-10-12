{ fail, haskellPackages, haskellPkgToAsts, haskellPkgToRawAsts, lib,
  makeHaskellPkgNixable, nix-config, nixedHsPkg, package, runCommand,
  tipBenchmarks, tipToHaskellPkg, unpack, withNix }:

with lib;
rec {
  tip = {
    example     = ../tests/example.smt2;
    list-full   = ../benchmarks/list-full.smt2;
    nat-full    = ../benchmarks/nat-full.smt2;
    nat-simple  = ../benchmarks/nat-simple.smt2;
    teBenchmark = tipBenchmarks.tip-benchmark-smtlib;
  };

  haskellPkgs = { script ? tipToHaskellPkg }:
    mapAttrs (n: f: runCommand "haskell-pkg-of-${n}"
      {
        inherit f;
        buildInputs = [ fail script ];
      }
      ''
        D=$(tipToHaskellPkg < "$f")
        [[ -e "$D" ]] || fail "'$D' doesn't exist"

        X=$(readlink -f "$D")
        [[ -d "$X" ]] || fail "'$X' isn't dir"

        ln -s "$X" "$out"
      '')
      tip // { testPackage = ../tests/testPackage; };

  haskellDrvs = mapAttrs (_: d: haskellPackages.callPackage d {})
                         (haskellNixed {});

  haskellNixed = { script ? makeHaskellPkgNixable }:
    mapAttrs (n: dir: runCommand "nixed-${n}"
                        {
                          inherit dir n;
                          inherit (nix-config) stableHackageDb;
                          buildInputs = [ fail script ];
                        }
                        ''
                          set -e
                          export HOME="$PWD"
                          ln -s "$stableHackageDb/.cabal" "$HOME/.cabal"

                          X=$(makeHaskellPkgNixable "$dir") ||
                            fail "Package $n failed to nixify"
                          ln -s "$X" "$out"
                        '')
             (haskellPkgs {} // {
               list-extras = unpack haskellPackages.list-extras.src;
             });

  asts = { script ? haskellPkgToRawAsts }:
    mapAttrs (n: drv: runCommand "asts-of-${n}"
                        {
                          src         = unpack drv.src;
                          buildInputs = [
                            (haskellPkgToAsts { inherit script; })
                          ];
                        }
                        ''
                          set -e
                          haskellPkgToAsts "$src" > "$out"
                        '')
             haskellDrvs;

  # Some of our examples are infeasible to explore, so we skip them
  eqs = { script ? quickspecAsts }:
    mapAttrs (n: asts: runCommand "eqs-of-${n}"
                         {
                           inherit asts;
                           buildInputs = [ script ];
                           OUT_DIR     = getAttr n (haskellNixed {});
                           MAX_SECS    = "180";
                           MAX_KB      = "2000000";
                         }
                         ''
                           set -e
                           quickspecAsts "$OUT_DIR" < "$asts" > "$out"
                         '')
             (removeAttrs (asts {}) [ "nat-full" "teBenchmark" ]);
}
