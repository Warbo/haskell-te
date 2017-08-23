{ attrsToDirs, bash, fail, gnugrep, gnused, jq, wrap }:

attrsToDirs {
  bin = {
    haskellPkgNameVersion = wrap {
      name   = "haskellPkgNameVersion";
      paths  = [ bash fail gnugrep gnused jq ];
      script = ''
        #!/usr/bin/env bash
        set   -e
        shopt -s nullglob

        [[ -n "$1" ]] || fail "haskellPkgNameVersion needs a dir as arg"
        [[ -e "$1" ]] || fail "haskellPkgNameVersion arg '$1' doesn't exist"

           NAME=""
        VERSION=""
          COUNT=0

        for CBL in "$1"/*.cabal
        do
          COUNT=$(( COUNT + 1 ))

             NAME=$(grep -i '^\s*name\s*:'    < "$CBL" | cut -d ':' -f 2 |
                                                         sed -e 's/\s//g')
          VERSION=$(grep -i '^\s*version\s*:' < "$CBL" | cut -d ':' -f 2 |
                                                         sed -e 's/\s//g')
        done

        [[ "$COUNT" -eq 1 ]] || fail "Found $COUNT .cabal files in '$1'"
        [[ -n "$NAME"    ]] || fail "Couldn't get project name from '$1'"
        [[ -n "$VERSION" ]] || fail "Couldn't get project version from '$1'"

        jq -n --arg name "$NAME" --arg version "$VERSION" \
           '{"package": $name, "version": $version}'
      '';
    };
  };
}
