{ attrsToDirs, dumpToNixScripts, fail, inNixedDir, jq, makeHaskellPkgNixable,
  runCommand, tipToHaskellPkg, withDeps, wrap }:

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
      nix-shell -p "import $EXPR" --run "'$main' '$DIR'" > ./rawAsts.json
    '';
  };

  haskellPkgToRawAsts = attrsToDirs {
    bin = {
      haskellPkgToRawAsts = wrap {
        name   = "haskellPkgToRawAsts";
        paths  = [ fail inNixedDir ];
        vars   = { inherit impureGetAsts; };
        script = ''
          #!/usr/bin/env bash
          set -e

          [[ -n "$1" ]] || fail "haskellPkgToRawAsts needs an arg"
          [[ -d "$1" ]] || fail "haskellPkgToRawAsts arg '$1' should be dir"

          # Get name and version from .cabal file
            pName=""
          version=""
          for CBL in "$1"/*.cabal
          do
              pName=$(grep -i '^\s*name\s*:'    < "$CBL" | cut -d ':' -f 2 |
                                                           sed -e 's/\s//g')
            version=$(grep -i '^\s*version\s*:' < "$CBL" | cut -d ':' -f 2 |
                                                           sed -e 's/\s//g')
          done

          [[ -n "$pName"   ]] || fail "Couldn't get project name from '$1'"
          [[ -n "$version" ]] || fail "Couldn't get project version from '$1'"

          export pName
          export nameVersion="{\"package\":\"$pName\",\"version\":\"$version\"}"

          DIR=$(readlink -f "$1")
          export DIR

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
