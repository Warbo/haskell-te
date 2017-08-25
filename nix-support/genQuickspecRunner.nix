{ bash, checkStderr, fail, gnugrep, gnused, haskellPackages, haveVar,
  inNixedDir, jq, makeWrapper, nix, nixEnv, quickspecBench, timeout, wrap }:

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
      haveVar fibblefoo

      echo "FIXME: NIXENV: ($NIXENV)" 1>&2
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
    paths  = [ bash fail gnused haveVar ];
    vars   = {
      inherit makeWrapper nixTemplate rawTemplate runner;
      escapeVar = "s/'/'\''/g";
    };
    script = ''
      #!/usr/bin/env bash
      set -e

      source "$makeWrapper/nix-support/setup-hook"

      function escapeVar {
        # Escape ', so we can wrap values in single quotes with confidence

        # Wrap in single quotes, but also surround in double quotes to bypass
        # the broken escaping of makeWrapper (it uses "foo", so by wrapping our
        # values in double quotes we get ""foo"", which is foo (our
        # single-quoted string) concatenated between two empty strings).
        echo "\"'$(echo "$1" | sed -e "$escapeVar")'\""
      }

      haveVar NIXENV
      haveVar CMD
      haveVar HASKELL_CODE

      function setArgs {
        makeWrapper "$runner" "$2"                                    \
          --set    RUNNER       "$1"                                  \
          --set    NIXENV       "$(echo "$NIXENV"       | escapeVar)" \
          --set    CMD          "$(echo "$CMD"          | escapeVar)" \
          --set    HASKELL_CODE "$(echo "$HASKELL_CODE" | escapeVar)"
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

      # Get the required environment, code and Haskell command
      GENERATED=$(echo "$QS" | runhaskell "$getCmd") || {
        echo -e "Given:\n$ALL\n" 1>&2
        echo -e "Chosen:\n$QS\n" 1>&2
        fail "Couldn't generate QuickSpec code"
      }

      # Encapsulate the command and code into a standalone script
      HASKELL_CODE=$(echo "$GENERATED" | jq -r '.code'  )
            NIXENV=$(echo "$GENERATED" | jq -r '.env'   )
               CMD=$(echo "$GENERATED" | jq -r '.runner')

      haveVar HASKELL_CODE
      haveVar NIXENV
      haveVar CMD

      export HASKELL_CODE
      export NIXENV
      export CMD

      inNixedDir "$encapsulate" "quickspec-runner"
    '';
  };
};
generateCode
