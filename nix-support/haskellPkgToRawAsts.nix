{ attrsToDirs, bash, dumpToNixScripts, fail, haskellPkgNameVersion, inNixedDir,
  jq, lib, makeHaskellPkgNixable, makeWrapper, nix, nixEnv, runCommand,
  testData, tipToHaskellPkg, withDeps, wrap, writeScript }:

with builtins;
with lib;
with rec {
  impureGetAsts = wrap {
    name  = "impureGetAsts";
    paths = [ nix ];
    vars  = {
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
        paths  = [
          fail haskellPkgNameVersion inNixedDir jq makeHaskellPkgNixable
        ];
        vars   = { inherit impureGetAsts; };
        script = ''
          #!/usr/bin/env bash
          set -e

          [[ -n "$1" ]] || fail "haskellPkgToRawAsts needs an arg"
          [[ -e "$1" ]] || fail "haskellPkgToRawAsts arg '$1' doesn't exist"

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

  testExamplePkg = n: pkg: runCommand "testRawAstsOf-${n}"
    (nixEnv // {
      inherit pkg;
      buildInputs = [ fail haskellPkgToRawAsts jq ];
    })
    ''
      set -o pipefail

      ASTS=$(haskellPkgToRawAsts "$pkg") || fail "Couldn't get ASTs"

      T=$(echo "$ASTS" | jq 'type')       || fail "Couldn't get type of: $ASTS"
      [[ "x$T" = 'x"array"' ]] || fail "Got '$T' instead of array"

      L=$(echo "$ASTS" | jq 'length') || fail "Couldn't get length"
      [[ "$L" -gt 3 ]]                || fail "Length '$L', expected a few"

      echo "pass" > "$out"
    '';

  checks = attrValues (mapAttrs testExamplePkg testData.haskellPkgs);
};

withDeps checks haskellPkgToRawAsts
