{ bash, bashEscape, checkStderr, fail, gnugrep, gnused, haskellPackages,
  haveVar, inNixedDir, jq, makeWrapper, nix, nixEnv, quickspecBench, timeout,
  wrap }:

with rec {
  inherit (quickspecBench) getCmd;

  keepJson  = wrap {
    name   = "keep-json";
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
    name   = "quickspec-runner";
    vars   = { inherit checkStderr keepJson; };
    paths  = [ bash haveVar timeout ];
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

      haveVar NIXENV
      haveVar CMD
      haveVar HASKELL_CODE
      haveVar RUNNER
      haveVar PKG_NAME
      haveVar NIX_EVAL_HASKELL_PKGS
      haveVar OUT_DIR

      function run {
        # Let users choose time/memory limits by wrapping in withTimout
        withTimeout "$RUNNER" 2> >("$checkStderr")
      }

      echo "$HASKELL_CODE" | run | "$keepJson"
    '';
  };

  nixTemplate = wrap {
    name   = "quickspec-nix-shell-template";
    paths  = [ bash haveVar nix ];
    script = ''
      #!/usr/bin/env bash
      set -e

      # This version uses nix-shell to ensure the correct environment; it's
      # the version we "export" for normal usage.
      haveVar NIXENV
      haveVar CMD

      nix-shell -p "$NIXENV" --run "$CMD"
    '';
  };

  rawTemplate = wrap {
    name   = "quickspec-raw-template";
    paths  = [ bash haveVar ];
    script = ''
      #!/usr/bin/env bash
      set -e

      # This version assumes that it's already in the correct environment.
      # This is fragile, so we don't export it to users. It's useful for
      # benchmarking since it avoids some of the Nix overhead.

      haveVar CMD

      $CMD
    '';
  };

  encapsulate = wrap {
    name   = "encapsulate-quickspec-runner";
    paths  = [ bash bashEscape fail gnused haveVar ];
    vars   = {
      inherit makeWrapper nixTemplate rawTemplate runner;
    };
    script = ''
      #!/usr/bin/env bash
      set -e

      source "$makeWrapper/nix-support/setup-hook"

      haveVar NIXENV
      haveVar CMD
      haveVar HASKELL_CODE

            ESC_NIXENV=$(echo "$NIXENV"       | bashEscape NIXENV)
               ESC_CMD=$(echo "$CMD"          | bashEscape CMD)
      ESC_HASKELL_CODE=$(echo "$HASKELL_CODE" | bashEscape HASKELL_CODE)

      function setArgs {
        makeWrapper "$runner" "$2"                  \
          --set    RUNNER       "$1"                \
          --set    NIXENV       "$ESC_NIXENV"       \
          --set    CMD          "$ESC_CMD"          \
          --set    HASKELL_CODE "$ESC_HASKELL_CODE"
      }

      setArgs "$nixTemplate" ./nixRunner
      setArgs "$rawTemplate" ./rawRunner
    '';
  };

  generateCode = wrap {
    name   = "generate-quickspec-code";
    paths  = [
      (haskellPackages.ghcWithPackages (h: [ h.mlspec h.nix-eval ]))
      fail haveVar inNixedDir jq nix
    ];
    vars   = nixEnv // {
      inherit encapsulate getCmd;
      NIX_EVAL_HASKELL_PKGS = builtins.toString ./quickspecEnv.nix;
    };
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

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

      # Encapsulate the command and code into a standalone script
      HASKELL_CODE=$(echo "$GENERATED" | jq -r '.code'  )
            NIXENV=$(echo "$GENERATED" | jq -r '.env'   )
               CMD=$(echo "$GENERATED" | jq -r '.runner')

      export HASKELL_CODE
      export NIXENV
      export CMD

      haveVar HASKELL_CODE
      haveVar NIXENV
      haveVar CMD

      inNixedDir "$encapsulate" "quickspec-runner"
    '';
  };
};
generateCode
