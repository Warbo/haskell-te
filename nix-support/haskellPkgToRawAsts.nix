{ bash, dumpToNixScripts, fail, haskellPkgNameVersion, inNixedDir, jq, lib,
  makeHaskellPkgNixable, mkBin, nix, nixEnv, runCommand, testData, withDeps }:

with builtins;
with lib;
with rec {
  impureGetAsts = mkBin {
    name   = "impureGetAsts";
    paths  = [ dumpToNixScripts.main nix ];
    vars   = { EXPR = toString ./dumpEnv.nix; };
    script = ''
      #!/usr/bin/env bash
      set -e

      nix-shell --show-trace -p "import $EXPR" \
                --run "dumpToNix '$OUT_DIR'" > ./rawAsts.json
    '';
  };

  haskellPkgToRawAsts = mkBin {
    name   = "haskellPkgToRawAsts";
    paths  = [
      fail haskellPkgNameVersion impureGetAsts inNixedDir jq
      makeHaskellPkgNixable
    ];
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

      D=$(inNixedDir impureGetAsts "getRawAstsFrom")
      [[ -f "$D/rawAsts.json" ]] || fail "Couldn't find raw ASTs"

      cat "$D/rawAsts.json"
    '';
  };

  testExamplePkg = n: asts: runCommand "testRawAstsOf-${n}"
    (nixEnv // {
      inherit asts;
      buildInputs = [ fail jq ];
    })
    ''
      set -o pipefail
      T=$(jq 'type' < "$asts") || fail "Couldn't get type of: $asts"
      [[ "x$T" = 'x"array"' ]] || fail "Got '$T' instead of array"

      L=$(jq 'length' < "$asts") || fail "Couldn't get length"
      [[ "$L" -gt 3 ]]           || fail "Length '$L', expected a few"

      mkdir "$out"
    '';

  checks = mapAttrs testExamplePkg
                    (testData.asts { script = haskellPkgToRawAsts; });
};

withDeps (attrValues checks) haskellPkgToRawAsts
