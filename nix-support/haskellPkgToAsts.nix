{ annotateRawAstsFrom, bash, explore, fail, haskellPkgToRawAsts, jq, lib,
  makeHaskellPkgNixable, mkBin, runCommand, testData, withDeps, withNix }:

{ script ? haskellPkgToRawAsts }:
with lib;
with rec {
  haskellPkgToAsts = mkBin {
    name   = "haskellPkgToAsts";
    paths  = [ annotateRawAstsFrom bash fail script makeHaskellPkgNixable ];
    vars   = {
      usage = ''
        haskellPkgToAsts extracts ASTs from the definitions made in a given
        Haskell project. A Haskell project is a directory containing a file
        whose name has a '.cabal' suffix.

        If the project doesn't have a default.nix file, we will try to make
        one using cabal2nix; if this causes problems, consider adding your
        own default.nix.

        ASTs are returned as JSON on stdout.
      '';
    };
    script = ''
      #!/usr/bin/env bash
      set   -e
      set   -o pipefail
      shopt -s nullglob

      [[ -n "$1" ]] || fail "Need argument (see --help)"

      if [[ "x$1" = "x--help" ]]
      then
        echo "$usage" 1>&2
        exit 0
      fi

      # Get a Nix expression for this package
      D=$(makeHaskellPkgNixable "$1") ||
        fail "Couldn't get Nix expression for package '$1'"

      haskellPkgToRawAsts "$D" | annotateRawAstsFrom "$D"
    '';
  };

  check = n: pkg: runCommand "test-haskellPkgToAsts-example"
    (withNix {
      inherit pkg;
      buildInputs = [ fail haskellPkgToAsts jq (explore.extractedEnv {
        standalone = pkg;
      }) ];
      SKIP_NIX = "1";
    })
    ''
      set -e
      ASTS=$(haskellPkgToAsts "$pkg" ) || fail "Command failed"

      T=$(echo "$ASTS" | jq -r 'type') || fail "Couldn't parse ASTs"
      [[ "x$T" = "xarray" ]] || fail "Expected array, got '$T'"

      L=$(echo "$ASTS" | jq 'length') || fail "Couldn't get length"
      [[ "$L" -gt 3 ]] || fail "Expected a few ASTs, found '$L'"

      mkdir "$out"
    '';

  checks = attrValues (mapAttrs check {
    inherit (testData.haskellNixed {}) test-theory;
  });
};

withDeps checks haskellPkgToAsts
