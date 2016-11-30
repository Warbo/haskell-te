defs: with defs;
with builtins;

let hasAttr = set: name: testWrap [(testMsg (set ? "${name}")
                                            "Have '${name}'")

                                   (testMsg (isAttrs set."${name}")
                                            "'${name}' is a set")]

                                   "Have set '${name}'";

    tests = map (hasAttr defs) [
              "mlspec"
            ] ++
            map (hasAttr haskellPackages) [
              "ArbitraryHaskell"
              "bench"
              "mlspec"
              "mlspec-helper"
              "nix-eval"
              "runtime-arbitrary"
              "weigh"
            ];
 in testWrap tests "All packages available"
