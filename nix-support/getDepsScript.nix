{ GetDeps, jq, utillinux, writeScript }:

writeScript "getDeps" ''
  #!/usr/bin/env bash

  function msg {
    echo -e "$1" 1>&2
  }

  "${jq}/bin/jq" -c '.[]' | while read -r LINE
  do
    DEPENDENCIES=$(echo "$LINE" | "${jq}/bin/jq" -r '.ast' | "${GetDeps}/bin/GetDeps")
    [[ -z "$DEPENDENCIES" ]] && msg "Unexpected line: $LINE"

    # Split versions from the package names
    VERSIONED=$(echo "$DEPENDENCIES" | "${jq}/bin/jq" -c '.[]' | while read -r DEP
    do
      PKG=$(echo "$DEP" | "${jq}/bin/jq" -cr '.package')
      if echo "$PKG" | grep -- "-[0-9][0-9.]*$" > /dev/null
      then
        # We have a version number in our package field; split it up
        NAME=$(echo    "$PKG" | "${utillinux}/bin/rev" | cut -d '-' -f 2- | "${utillinux}/bin/rev")
        VERSION=$(echo "$PKG" | "${utillinux}/bin/rev" | cut -d '-' -f 1  | "${utillinux}/bin/rev")

        # shellcheck disable=SC2016
        echo "$DEP" | "${jq}/bin/jq" --arg name "$NAME"       \
                                     --arg version "$VERSION" \
                                     '. + {"package":$name,"version":$version}'
      else
        # We don't have a version number in our package field; leave as-is
        echo "$DEP"
      fi
    done | "${jq}/bin/jq" -s '.')

    # Add the dependencies to the object
    echo "$LINE" | "${jq}/bin/jq" -c ". + {\"dependencies\": $VERSIONED }"
  done  | "${jq}/bin/jq" -s '.'
''
