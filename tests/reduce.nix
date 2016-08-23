defs: with defs;

testRun "reduce-equations test suite" null
        {
          d = haskellPackages.reduce-equations.src;
          buildInputs = [
            cabal-install
            (haskellPackages.ghcWithPackages (h: [
              h.reduce-equations
              h.bytestring
              h.containers
              h.directory
              h.tasty
              h.tasty-quickcheck
            ]))
          ];
        }
        ''
          export HOME="$PWD"
          cp -r "$d" ./src
          chmod +w -R ./src
          cd ./src
          ./test.sh || exit 1
        ''
