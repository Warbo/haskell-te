{ bash, coreutils, explore, jq, lib, mkBin, nixListToBashArray, sanitise, strip,
  time, wrap, writeScript }:

with builtins; with lib;

rec {
  # A quick and dirty sanity check
  checkStderr = mkBin {
    name   = "checkStderr";
    paths  = [ bash ];
    vars   = {
      knownErrors = writeScript "known-errors" ''
        jq: error
        MLSpec: Failed
        syntax error
        Argument list too long
        out of memory
        parse error:
        ^error:
      '';
    };
    script = ''
      #!/usr/bin/env bash
      set -e

      ERR=""

      function check() {
        while read -r LINE
        do
          # Spit out line so user can see it
          echo "$LINE" 1>&2

          # Check if it contains an error
          if echo "$LINE" | grep -f "$knownErrors" > /dev/null
          then
            ERR="$ERR $1"
          fi
        done
      }

      # Check stdin if it's not a TTY
      if ! [ -t 0 ]
      then
        cat | check "stdin (NOTE: May have been redirected from stderr)"
      fi

      # Check any given args
      for F in "$@"
      do
        check "$F" < "$F"
      done

      [[ -z "$ERR" ]] || {
        echo "Errors found in$ERR" 1>&2
        exit 2
      }

      exit
    '';
  };

  # Check that the required Haskell packages are found in the environment
  checkHsEnv = extra:
    let allGiven = extra ++ explore.extra-haskell-packages;
     in writeScript "checkHsEnv" ''
          #!/usr/bin/env bash
          set -e
          set -o pipefail

          function ensurePkg {
            # Skip empty lines
            echo "$1" | grep '[a-zA-Z_]' > /dev/null || return 0

            if ghc-pkg list "$1" | grep "$1" > /dev/null
            then
              return 0
            fi

            echo "Aborting. Didn't find Haskell package '$1' in" 1>&2
            ghc-pkg list 1>&2
            exit 1
          }

          # We must have ghc-pkg, or else we can't even check the others
          command -v "ghc-pkg" > /dev/null 2>&1 || {
            echo "No ghc-pkg command in environment" 1>&2
            exit 1
          }

          # '|| true' to appease 'set -e' when we have no input
          INPUT=""
          [ -t 0 ] || INPUT=$(sort -u | grep "^." | cut -c1-128) || true

          if [[ -n "$INPUT" ]]
          then
            while read -r PKG
            do
              ensurePkg "$PKG"
            done < <(echo "$INPUT"    |
                     grep '[a-zA-Z_]' |
                     "${explore.findHsPkgReferences}")
          fi

          while read -r PKG
          do
            ensurePkg "$PKG"
          done < <(echo "${concatStringsSep "\n" allGiven}")

          exit 0
        '';

  # Run commands with extra info for debugging and reproducability:
  #  - Store the given command, arguments, stdin, stdout and stderr
  #  - Force an error if stderr matches some known error pattern
  runCmd = { cmd, args ? [], inputs ? []}:
    # Stores the args in variables ARGS1, ARGS2, etc. and provides a code
    # snippet which collects them up into a bash array ARGS. This is better than
    # splicing into the build script, since it avoids unnecessary forcing and
    # eval-time building.
    with nixListToBashArray {
      inherit args;
      name = "ARGS";
    };
    wrap {
      name   = "run-cmd-${sanitise (unsafeDiscardStringContext
                                     (baseNameOf cmd))}";
      paths  = [ bash checkStderr ];
      vars   = env // { inherit cmd; };
      script = ''
         #!/usr/bin/env bash
         set -e

         # Sets up the ARGS array
         ${code}

         # Unset ARGS1, ARGS2, etc. to avoid polluting the environment of $cmd
         ${concatStringsSep "\n" (map (n: "unset " + n) (attrNames env))}

         # Run with the given arguments and check stderr for error messages
         "$cmd" "''${ARGS[@]}" > "$out" 2> >(checkStderr)
         CODE="$?"
         sleep 1  # For checkStderr (hacky and racy)
         exit "$?"
       '';
    };
}
