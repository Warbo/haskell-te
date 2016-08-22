defs: with defs;
with builtins;

testRun "ML4HSFE test suite" null
        { ml4hsfe = haskellPackages.ML4HSFE.src;
          buildInputs = [ (haskellPackages.ghcWithPackages (h: [
                            h.cabal-install h.ghc h.ML4HSFE h.quickspec h.tasty
                            h.tasty-quickcheck
                          ]))
                          runWeka ]; }
        ''
          set -e
          export HOME="$PWD"
          cp -r "$ml4hsfe" ./ml4hsfe
          chmod +w -R ./ml4hsfe
          cd ./ml4hsfe
          ./test.sh
        ''
