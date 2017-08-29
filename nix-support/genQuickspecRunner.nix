{ bash, bashEscape, checkStderr, fail, gnugrep, gnused, haskellPackages,
  haskellPkgNameVersion, haveVar, inNixedDir, jq, makeWrapper, mkBin, nix,
  nixEnv, quickspecBench, timeout, wrap, writeScript }:

with rec {
  inherit (quickspecBench) getCmd;

  keepJson  = mkBin {
    name   = "keepJson";
    paths  = [ bash gnugrep jq ];
    script = ''
      #!/usr/bin/env bash
      set -e

      # Strip out cruft that QuickSpec puts on stdout. Since this is just a
      # filter, we don't actually care if grep finds anything or not; hence
      # we use '|| true' to avoid signalling an error
      function strip {
        grep -v '^Depth' || true
      }

      strip | jq -s '.'
    '';
  };

  runner = wrap {
    name   = "quickspecRunner";
    paths  = [ bash checkStderr haveVar keepJson timeout ];
    vars   = { NIX_EVAL_HASKELL_PKGS = toString ./quickspecEnv.nix; };
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

      haveVar CMD
      haveVar HASKELL_CODE
      haveVar PKG_NAME
      haveVar NIX_EVAL_HASKELL_PKGS
      haveVar OUT_DIR

      function run {
        # Let users choose time/memory limits by wrapping in withTimout
        withTimeout $CMD 2> >(checkStderr)
      }

      echo "$HASKELL_CODE" | run | keepJson
    '';
  };

  generateCode = mkBin {
    name   = "genQuickspecRunner";
    paths  = [
      (haskellPackages.ghcWithPackages (h: [ h.mlspec h.nix-eval ]))
      fail haskellPkgNameVersion haveVar inNixedDir jq nix
    ];
    vars   = nixEnv // {
      inherit getCmd runner;
      NIX_EVAL_HASKELL_PKGS = builtins.toString ./quickspecEnv.nix;
      mkCmd = writeScript "quickspec-builder.nix" ''
        with builtins;
        assert getEnv "NIXENV"   != "" || abort "No NIXENV set";
        assert getEnv "OUT_DIR"  != "" || abort "No OUT_DIR set";
        assert getEnv "PKG_NAME" != "" || abort "No PKG_NAME set";
        assert getEnv "CMD"      != "" || abort "No CMD set";
        (import ${toString ../nix-support} {}).wrap {
          name  = "quickspec-runner";
          paths = [ (import (toFile "env.nix" (getEnv "NIXENV"))) ];
          vars  = {
            CMD          = getEnv("CMD");
            HASKELL_CODE = getEnv("HASKELL_CODE");
            OUT_DIR      = getEnv("OUT_DIR");
            PKG_NAME     = getEnv("PKG_NAME");
          };
          file  = getEnv("runner");
        }
      '';
    };
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

      haveVar OUT_DIR

      PKG_NAME=$(haskellPkgNameVersion "$OUT_DIR" | jq -r '.package')
      export PKG_NAME

      ALL=$(cat)
       QS=$(echo "$ALL" | jq 'map(select(.quickspecable))')

      echo "$QS" | jq -e 'length | . > 0' > /dev/null ||
        fail "Nothing quickspecable ($QS) in ($ALL)"

      # Get the required environment, code and Haskell command
      GENERATED=$(echo "$QS" | "$getCmd") || {
        echo -e "Given:\n$ALL\n" 1>&2
        echo -e "Chosen:\n$QS\n" 1>&2
        fail "Couldn't generate QuickSpec code"
      }
      [[ -n "$GENERATED" ]] || fail "Empty GENERATED"

      HASKELL_CODE=$(echo "$GENERATED" | jq -r '.code'  )
            NIXENV=$(echo "$GENERATED" | jq -r '.env'   )
               CMD=$(echo "$GENERATED" | jq -r '.runner')

      export  HASKELL_CODE
      haveVar HASKELL_CODE
      export  NIXENV
      haveVar NIXENV
      export  CMD
      haveVar CMD

      # Encapsulate the command and code into a standalone script
      nix-build --no-out-link --show-trace -E 'import (builtins.getEnv "mkCmd")'
    '';
  };
};
generateCode
