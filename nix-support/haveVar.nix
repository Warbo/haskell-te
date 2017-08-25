{ attrsToDirs, bash, fail, wrap }:

attrsToDirs {
  bin = {
    haveVar = wrap {
      name   = "haveVar";
      paths  = [ bash fail ];
      script = ''
        #!/usr/bin/env bash
        set -e

        [[ -n "$1"      ]] || fail "No var given to check"
        [[ -n "''${!1}" ]] || fail "No '$1' variable set"

        exit 0
      '';
    };
  };
}
