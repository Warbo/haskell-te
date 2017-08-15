{ bash, GetDeps, jq, utillinux, wrap, writeScript }:

wrap {
  name   = "getDeps";
  paths  = [ bash jq GetDeps utillinux ];
  script = ''
    #!/usr/bin/env bash
    set -e

    function msg {
      echo -e "$1" 1>&2
    }

    jq -c '.[]' | while read -r LINE
    do
      DEPENDENCIES=$(echo "$LINE" | jq -r '.ast' | GetDeps)
      [[ -n "$DEPENDENCIES" ]] || msg "Unexpected line: $LINE"

      # Split versions from the package names
      VERSIONED=$(echo "$DEPENDENCIES" | jq -c '.[]' | while read -r DEP
      do
        PKG=$(echo "$DEP" | jq -cr '.package')
        if echo "$PKG" | grep -- "-[0-9][0-9.]*$" > /dev/null
        then
          # We have a version number in our package field; split it up
             NAME=$(echo "$PKG" | rev | cut -d '-' -f 2- | rev)
          VERSION=$(echo "$PKG" | rev | cut -d '-' -f 1  | rev)

          echo "$DEP" | jq --arg name "$NAME"       \
                           --arg version "$VERSION" \
                           '. + {"package":$name,"version":$version}'
        else
          # We don't have a version number in our package field; leave as-is
          echo "$DEP"
        fi
      done | jq -s '.')

      # Add the dependencies to the object
      echo "$LINE" | jq -c ". + {\"dependencies\": $VERSIONED }"
    done  | jq -s '.'
  '';
}
