{ bash, checkStderr, lib, nixListToBashArray, sanitiseName, unlines, wrap }:

with builtins; with lib;

# Run commands with extra info for debugging and reproducability:
#  - Store the given command, arguments, stdin, stdout and stderr
#  - Force an error if stderr matches some known error pattern
{ cmd, args ? [], inputs ? []}:
  # Stores the args in variables ARGS1, ARGS2, etc. and provides a code
  # snippet which collects them up into a bash array ARGS. This is better than
  # splicing into the build script, since it avoids unnecessary forcing and
  # eval-time building.
  with nixListToBashArray { inherit args; name = "ARGS"; } // {
    sanitised = sanitiseName (unsafeDiscardStringContext (baseNameOf cmd));
  };
  wrap {
    name   = "run-cmd-${sanitised}";
    paths  = [ bash checkStderr ];
    vars   = env // { inherit cmd; };
    script = ''
       #!/usr/bin/env bash
       set -e

       # Sets up the ARGS array
       ${code}

       # Unset ARGS1, ARGS2, etc. to avoid polluting the environment of $cmd
       ${unlines (map (n: "unset " + n) (attrNames env))}

       # Run with the given arguments and check stderr for error messages
       "$cmd" "''${ARGS[@]}" 2> >(checkStderr)
       CODE="$?"
       sleep 1  # For checkStderr (FIXME: hacky and racy)
       exit "$?"
     '';
  }
