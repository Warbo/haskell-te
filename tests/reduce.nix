defs: with defs;

testRun "reduce-equations test suite" null
        {
          LANG           = "en_US.UTF-8";
          LOCALE_ARCHIVE = "${glibcLocales}/lib/locale/locale-archive";

          d = reduce-equations.src;

          buildInputs = [
            cabal-install
            (haskellPackages.ghcWithPackages (h: [
              h.bytestring
              h.containers
              h.directory
              h.MissingH
              h.tasty
              h.tasty-quickcheck
              h.reduce-equations
            ]))
          ];
        }
        ''
          export HOME="$PWD"
          cabal update
          cp -r "$d" ./src
          chmod +w -R ./src
          cd ./src
          ./test.sh || exit 1
        ''
