{ annotated, cabal-install, fail, glibcLocales, haskellPackages, jq, lib,
  runCommand, testData, unpack, withDeps }:

with builtins;
with lib;
with rec {
  inherit (haskellPackages) reduce-equations;

  testSuite = runCommand "reduce-equations-test-suite"
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

  checkGetEqs = attr: eqs: runCommand "reduceProducesEqs-${attr}"
    {
      inherit eqs;
      buildInputs = [ fail jq reduce-equations ];
    }
    ''
      set -e

      function die {
        echo "$GOT" 1>&2
        fail "$*"
      }

      GOT=$(reduce-equations < "$eqs")                 || die "Couldn't reduce"
      echo "$GOT" | jq -e 'type == "array"'            || die 'Not array'
      echo "$GOT" | jq -e 'map(has("relation")) | all' || die 'Not relation'

      mkdir "$out"
    '';
};

withDeps ([ testSuite ] ++ attrValues (mapAttrs checkGetEqs
                                                (testData.eqs {})))
         reduce-equations
