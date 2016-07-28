defs: with defs;
with builtins;

let hasAttr = set: name: testWrap [(testMsg (set ? "${name}")
                                            "Have '${name}'")

                                   (testMsg (isAttrs set."${name}")
                                            "'${name}' is a set")]

                                   "Have set '${name}'";

    tests = map (hasAttr defs) [
              "mlspec"
              "mlspec-bench"
            ] ++
            map (hasAttr haskellPackages) [
              "ArbitraryHaskell"
              "mlspec"
              "mlspec-bench"
              "mlspec-helper"
              "nix-eval"
              "runtime-arbitrary"
            ];
 in testWrap tests "All packages available"
