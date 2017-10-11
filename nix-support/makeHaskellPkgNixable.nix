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

      [[ "$COUNT" -eq 1 ]] ||
        fail "No .cabal in '$1'; is it a build output? (We need the source)"
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

      DIR=$(readlink -f "$1")
      if [[ -d "$DIR" ]]
      then
        hasCabalFile "$DIR" || fail "Need .cabal file, aborting"
        if [[ -e "$DIR/default.nix" ]]
        then
          echo "$DIR"
        else
          DIR="$DIR" inNixedDir addNixFile "withAddedNixFile"
        fi
      else
        fail "Not a directory (or symlink) '$1'"
      fi
    '';
  };

  testMakeHaskellPkgNixable = mapAttrs
    (n: nixed: runCommand "testMakeHaskellPkgNixable-${n}"
      (withNix {
        inherit n nixed;
        buildInputs = [ fail ];
        expr        = ''builtins.typeOf (import (builtins.getEnv "F"))'';
      })
      ''
        set -e

        [[ -n "$nixed" ]] || fail "No output for package $n"
        Y=$(readlink -f "$nixed")
        [[ -d "$Y" ]] || fail "Didn't make nixified dir for $n: '$nixed' ($Y)"

        T=$(F="$Y" nix-instantiate --show-trace --eval -E "$expr") ||
          fail "Output for $n didn't parse"
        [[ "x$T" = 'x"lambda"' ]] || fail "Expr type of $n was '$T'"

        mkdir "$out"
      '')
    (testData.haskellNixed { script = makeHaskellPkgNixable; });
};

withDeps ([ testHasCabalFile ] ++ (attrValues testMakeHaskellPkgNixable))
         makeHaskellPkgNixable
