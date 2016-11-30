{ bash, coreutils, explore, lib, runScript, strip, time, writeScript }:

with builtins; with lib;

rec {

  # A quick and dirty sanity check
  knownErrors = writeScript "known-errors" ''
    jq: error
    MLSpec: Failed
    syntax error
    Argument list too long
    out of memory
    parse error:
    ^error:
  '';

  checkStderr = writeScript "check-stderr" ''
    #!${bash}/bin/bash
    set -e
    if grep -f "${knownErrors}" < "$1" 1>&2
    then
      echo "Errors found in '$1'" 1>&2
      exit 2
    fi
    exit
  '';

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
  #  - Optionally, benchmark the command

  runCmd = { cmd, args ? [], inputs ? []}:
   let shellArgs = map escapeShellArg args;
       argStr    = concatStringsSep " " shellArgs;
       name      = unsafeDiscardStringContext (baseNameOf cmd);
    in trace "FIXME: Move DO_BENCH into here" writeScript "run-cmd-${name}" ''
         #!${bash}/bin/bash

         # Store our input
         cat > stdin

         # Check that all Haskell packages references in our input are available
         # to GHC
         "${checkHsEnv []}" < stdin || {
           echo "checkHsEnv failed" 1>&2
           exit 1
         }

         # Run the given command; we tee stderr so the user can still see it
         "${cmd}" ${argStr} < stdin 1> stdout 2> >(tee stderr >&2)
         CODE="$?"

         # Put results in the Nix store, so we make better use of the cache and
         # avoid sending huge strings into Nix
          STDIN=$(nix-store --add stdin)
         STDOUT=$(nix-store --add stdout)
         STDERR=$(nix-store --add stderr)

         FAILED=false
         if [[ "$CODE" -ne 0 ]]
         then
           echo "Failed to run '${cmd}' with '${argStr}'" 1>&2

           echo "Contents of stdin:"  1>&2
           cat  stdin                 1>&2 || true
           echo "End of stdin"        1>&2

           echo "Contents of stderr:" 1>&2
           cat  stderr                1>&2 || true
           echo "End of stderr"       1>&2

           echo "Contents of stdout:" 1>&2
           cat  stdout                1>&2 || true
           echo "End of stdout"       1>&2

           FAILED=true
         elif ! "${checkStderr}" "$STDERR"
         then
           echo "Errors found in '$STDERR' for '${cmd}'" 1>&2
           FAILED=true
         else
           echo "Finished running '${cmd}'" 1>&2
         fi

         # Make report
         jq -n --arg     cmd    '${cmd}'         \
               --argjson args   '${toJSON args}' \
               --arg     stdin  "$STDIN"         \
               --arg     stdout "$STDOUT"        \
               --arg     stderr "$STDERR"        \
               --argjson failed "$FAILED"        \
               '{"failed"   : $failed,
                 "cmd"      : $cmd,
                 "args"     : $args,
                 "stdin"    : $stdin,
                 "stdout"   : $stdout,
                 "stderr"   : $stderr}'
       '';
}
