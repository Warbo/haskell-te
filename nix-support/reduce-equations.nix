{ annotated, cabal-install, glibcLocales, haskellPackages, jq, lib, nixedHsPkg,
  quickspecAsts, runCommand, testData, unpack, withDeps }:

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

  checkGetEqs = attr: pkg:
    with rec {
      name = pkg.name;
      eqs  = runCommand "eqs-of-${name}"
        {
          asts        = annotated { pkgDir = unpack pkg.src; };
          buildInputs = [ quickspecAsts ];
          OUT_DIR     = nixedHsPkg (unpack pkg.src);
        }
        ''
          set -e
          quickspecAsts < "$asts" > "$out"
        '';
    };
    runCommand "reduceProducesEqs-${name}"
      {
        inherit eqs;
        buildInputs = [ jq reduce-equations ];
      }
      ''
        set -e
        GOT=$(reduce-equations < "$eqs")
        echo "$GOT" | jq -e 'type == "array"'
        echo "$GOT" | jq -e 'map(has("relation")) | all' > "$out"
      '';
};

withDeps ([ testSuite ] ++ attrValues (mapAttrs checkGetEqs
                                                testData.haskellDrvs))
         reduce-equations
