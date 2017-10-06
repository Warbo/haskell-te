{ bash, fail, inNixedDir, lib, mkBin, runCommand, tipBenchmarks, testData,
  withDeps }:

with builtins;
with lib;
with rec {
  genPkgHere = mkBin {
    name  = "genPkgHere";
    paths = [ bash tipBenchmarks.tools ];
    script = ''
      #!/usr/bin/env bash
      OUT_DIR="$PWD" full_haskell_package
    '';
  };

  tipToHaskellPkg = mkBin {
    name   = "tipToHaskellPkg";
    paths  = [ bash genPkgHere inNixedDir ];
    script = ''
      #!/usr/bin/env bash
      inNixedDir genPkgHere "haskellPkgGeneratedFromTip"
    '';
  };

  checks = mapAttrs
    (n: f: runCommand "test-tipToHaskellPkg-${n}"
      {
        inherit f;
        buildInputs = [ fail tipToHaskellPkg ];
      }
      ''
        shopt -s nullglob

        command -v tipToHaskellPkg  || fail "No tipToHaskellPkg program"

        PRECRUFT=0
        for X in ./*
        do
          PRECRUFT=$(( PRECRUFT + 1 ))
        done

        D=$(tipToHaskellPkg < "$f") || fail "tipToHaskellPkg failed"

        [[ -n "$D" ]] || fail "Got no output"
        Z=$(readlink -f "$D")
        [[ -d "$Z" ]] || fail "Result '$D' ($Z) isn't directory"

        echo "Result is '$D'" 1>&2

        GOTCABAL=0
        for CBL in "$D"/*.cabal
        do
          GOTCABAL=1
        done
        [[ "$GOTCABAL" -eq 1 ]] || fail "Found $GOTCABAL .cabal files"

        POSTCRUFT=0
        for X in ./*
        do
          POSTCRUFT=$(( POSTCRUFT + 1 ))
        done
        [[ "$PRECRUFT" -eq "$POSTCRUFT" ]] ||
          fail "PWD has '$POSTCRUFT' entries; did have '$PRECRUFT'"

        echo pass > "$out"
      '')
    testData.tip;
};

withDeps (attrValues checks) tipToHaskellPkg
