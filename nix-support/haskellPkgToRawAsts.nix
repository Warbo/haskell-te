{ attrsToDirs, dumpToNixScripts, fail, haskellPkgNameVersion, inNixedDir, jq,
  makeHaskellPkgNixable, runCommand, tipToHaskellPkg, withDeps, wrap }:

with builtins;
with rec {
  impureGetAsts = wrap {
    name = "impureGetAsts";
    vars = {
      inherit (dumpToNixScripts) main;
      EXPR = toString ./dumpEnv.nix;
    };
    script = ''
      #!/usr/bin/env bash
      set -e

      nix-shell --show-trace -p "import $EXPR" \
                --run "'$main' '$OUT_DIR'" > ./rawAsts.json
    '';
  };

  haskellPkgToRawAsts = attrsToDirs {
    bin = {
      haskellPkgToRawAsts = wrap {
        name   = "haskellPkgToRawAsts";
        paths  = [ fail haskellPkgNameVersion inNixedDir jq ];
        vars   = { inherit impureGetAsts; };
        script = ''
          #!/usr/bin/env bash
          set -e

          [[ -n "$1" ]] || fail "haskellPkgToRawAsts needs an arg"
          [[ -d "$1" ]] || fail "haskellPkgToRawAsts arg '$1' should be dir"

          # Get name and version from .cabal file
          nameVersion=$(haskellPkgNameVersion "$1")
          export nameVersion

          pName=$(echo "$nameVersion" | jq -r '.package')
          export pName

          OUT_DIR=$(makeHaskellPkgNixable "$1")
          export OUT_DIR

          D=$(inNixedDir "$impureGetAsts" "getRawAstsFrom")
          [[ -f "$D/rawAsts.json" ]] || fail "Couldn't find raw ASTs"

          cat "$D/rawAsts.json"
        '';
      };
    };
  };

  testExamplePkg = runCommand "rawAstsOfExample"
    {
      buildInputs = [ fail haskellPkgToRawAsts jq ];
      example     = ../tests/testPackage;
    }
    ''
      set -o pipefail

      ASTS=$(haskellPkgToRawAsts "$example") || fail "Couldn't get ASTs"

      T=$(echo "$ASTS" | jq 'type')       || fail "Couldn't get type of: $ASTS"
      [[ "x$T" = 'x"array"' ]] || fail "Got '$T' instead of array"

      L=$(echo "$ASTS" | jq 'length') || fail "Couldn't get length"
      [[ "$L" -gt 3 ]]                || fail "Length '$L', expected a few"

      echo "pass" > "$out"
    '';

  testWithTip = f: runCommand "rawAstsOfTip-${unsafeDiscardStringContext
                                                (baseNameOf f)}"
    {
      inherit f;
      buildInputs = [ fail haskellPkgToRawAsts jq makeHaskellPkgNixable
                      tipToHaskellPkg ];
    }
    ''
      set -e
      set -o pipefail
      DIR=$(tipToHaskellPkg       < "$f") || fail "Couldn't turn '$f' into pkg"
      NIX=$(makeHaskellPkgNixable "$DIR") || fail "Couldn't nixify '$DIR'"
      RAW=$(haskellPkgToRawAsts   "$NIX") || fail "Couldn't get ASTs of '$DIR'"

      L=$(echo "$RAW" | jq 'length') || fail "Couldn't get length of '$RAW'"
      [[ "$L" -gt 3 ]] || fail "Got '$L' raw ASTs, expected a few"

      echo pass > "$out"
    '';

  checks = [ testExamplePkg ] ++ map testWithTip [
    ../benchmarks/nat-full.smt2
    ../benchmarks/nat-simple.smt2
    ../benchmarks/list-full.smt2

  ];
};

withDeps checks haskellPkgToRawAsts
