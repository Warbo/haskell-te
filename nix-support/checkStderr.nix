# A quick and dirty sanity check
{ bash, mkBin, writeScript }:

mkBin {
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
}
