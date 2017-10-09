{ cabal-install, glibcLocales, haskellPackages, runCommand, withDeps }:

with rec {
  inherit (haskellPackages) reduce-equations;

  test = runCommand "reduce-equations-test-suite"
    {
      inherit (reduce-equations) src;
      LANG           = "en_US.UTF-8";
      LOCALE_ARCHIVE = "${glibcLocales}/lib/locale/locale-archive";
      buildInputs    = [
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
      set -e
      export HOME="$PWD"
      cabal update
      cp -r "$src" ./src
      chmod +w -R ./src
      cd ./src
      ./test.sh
      mkdir "$out"
    '';
};

withDeps [ test ] reduce-equations
