{ attrsToDirs, bash, cabal2nix, fail, inNixedDir, lib, mkBin, nix-config,
  pipeToNix, runCommand, testData, withDeps, withNix }:

with builtins;
with lib;
with rec {
  hasCabalFile = mkBin {
    name   = "hasCabalFile";
    paths  = [ bash fail ];
    script = ''
      #!/usr/bin/env bash
      set   -e
      shopt -s nullglob

      COUNT=0
      for F in "$1"/*.cabal
      do
        COUNT=$(( COUNT + 1 ))
      done

      [[ "$COUNT" -eq 1 ]] || fail "No cabal files found in '$1'"
    '';
  };

  testHasCabalFile = runCommand "test-hasCabalFile"
    rec {
      foo     = toFile "foo" "foo";
      tooFew  = attrsToDirs { inherit foo;       bar         = foo; };
      justOne = attrsToDirs { "foo.cabal" = foo; bar         = foo; };
      tooMany = attrsToDirs { "foo.cabal" = foo; "bar.cabal" = foo; };
      buildInputs = [ fail hasCabalFile ];
    }
    ''
      if hasCabalFile "$tooFew"
      then
        fail "Should have been too few"
      fi

      if hasCabalFile "$tooMany"
      then
        fail "Should have been too many"
      fi

      hasCabalFile "$justOne" || fail "Should've worked for one .cabal file"

      echo pass > "$out"
    '';

  addNixFile = mkBin {
    name   = "addNixFile";
    paths  = [ bash cabal2nix ];
    script = ''
      #!/usr/bin/env bash
      set -e
      shopt -s nullglob
      shopt -s dotglob

      cp -a "$DIR"/* ./
      chmod +w -R ./*

      cabal2nix ./. > default.nix
    '';
  };

  makeHaskellPkgNixable = mkBin {
    name   = "makeHaskellPkgNixable";
    paths  = [ addNixFile cabal2nix fail hasCabalFile inNixedDir pipeToNix ];
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

      if [[ -d "$1" ]]
      then
        DIR=$(readlink -f "$1")
        hasCabalFile "$DIR" || fail "Need .cabal file, aborting"
        if [[ -e "$DIR/default.nix" ]]
        then
          echo "$DIR"
        else
          DIR="$DIR" inNixedDir addNixFile "withAddedNixFile"
        fi
      else
        fail "Not a directory '$1'"
      fi
    '';
  };

  testMakeHaskellPkgNixable = mapAttrs
    (n: p: runCommand "testMakeHaskellPkgNixable-${n}"
      (withNix {
        inherit n p;
        inherit (nix-config) stableHackageDb;
        buildInputs = [ fail makeHaskellPkgNixable ];
        expr        = ''builtins.typeOf (import (builtins.getEnv "F"))'';
      })
      ''
        export HOME="$PWD"
        ln -s "$stableHackageDb/.cabal" "$HOME/.cabal"

        X=$(makeHaskellPkgNixable "$p") || fail "Package $n failed"
        [[ -n "$X" ]] || fail "No output for package $n"
        [[ -d "$X" ]] || fail "Didn't make nixified dir for $n: '$X'"

        T=$(F="$X" nix-instantiate --show-trace --eval -E "$expr") ||
          fail "Output for $n didn't parse"
        [[ "x$T" = 'x"lambda"' ]] || fail "Expr type of $n was '$T'"

        echo pass > "$out"
      '')
    testData.haskellPkgs;
};

withDeps ([ testHasCabalFile ] ++ (attrValues testMakeHaskellPkgNixable))
         makeHaskellPkgNixable
