{ attrsToDirs, bash, bzip2, cabal2nix, fail, gnutar, gzip, inNixedDir,
  nix-config, pipeToNix, runCommand, withDeps, withNix, wrap, xz }:

with builtins;
with rec {
  hasCabalFile = wrap {
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
      inherit hasCabalFile;
      foo     = toFile "foo" "foo";
      tooFew  = attrsToDirs { inherit foo;       bar         = foo; };
      justOne = attrsToDirs { "foo.cabal" = foo; bar         = foo; };
      tooMany = attrsToDirs { "foo.cabal" = foo; "bar.cabal" = foo; };
      buildInputs = [ fail ];
    }
    ''
      if "$hasCabalFile" "$tooFew"
      then
        fail "Should have been too few"
      fi

      if "$hasCabalFile" "$tooMany"
      then
        fail "Should have been too many"
      fi

      "$hasCabalFile" "$justOne" || fail "Should've worked for one .cabal file"

      echo pass > "$out"
    '';

  addNixFile = wrap {
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

  makeHaskellPkgNixable = attrsToDirs {
    bin = {
      makeHaskellPkgNixable = wrap {
        name   = "makeHaskellPkgNixable";
        paths  = [ cabal2nix fail inNixedDir pipeToNix ];
        vars   = { inherit addNixFile hasCabalFile; };
        script = ''
          #!/usr/bin/env bash
          set -e
          set -o pipefail

          if [[ -d "$1" ]]
          then
            DIR=$(readlink -f "$1")
            "$hasCabalFile" "$DIR" || fail "Need .cabal file, aborting"
            if [[ -e "$DIR/default.nix" ]]
            then
              echo "$DIR"
            else
              DIR="$DIR" inNixedDir "$addNixFile" "withAddedNixFile"
            fi
          else
            fail "Not a directory '$1'"
          fi
        '';
      };
    };
  };

  testMakeHaskellPkgNixable = runCommand "testMakeHaskellPkgNixable"
    (withNix {
      inherit (nix-config) stableHackageDb;
      buildInputs = [ fail makeHaskellPkgNixable ];
      example     = ../tests/testPackage;
      expr        = ''builtins.typeOf (import (builtins.getEnv "F"))'';
    })
    ''
      export HOME="$PWD"
      ln -s "$stableHackageDb/.cabal" "$HOME/.cabal"

      X=$(makeHaskellPkgNixable "$example") || fail "Example failed"
      [[ -n "$X" ]] || fail "No output for example"
      [[ -d "$X" ]] || fail "Didn't make nixified dir for example: '$X'"

      T=$(F="$X" nix-instantiate --show-trace --eval -E "$expr") ||
        fail "Example output didn't parse"
      [[ "x$T" = 'x"lambda"' ]] || fail "Example type was '$T'"

      echo pass > "$out"
    '';
};

withDeps [ testHasCabalFile testMakeHaskellPkgNixable ] makeHaskellPkgNixable
