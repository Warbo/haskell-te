{ bash, fail, gnugrep, mkBin }:

mkBin {
  name   = "haveVar";
  paths  = [ bash fail gnugrep ];
  script = ''
    #!/usr/bin/env bash
    set -e

    [[ "$#" -eq 1 ]] || fail "haveVar needs 1 arg, given $#"

    echo "''${!1}" | grep '\S' > /dev/null || fail "No '$1' variable set"

    exit 0
  '';
}
