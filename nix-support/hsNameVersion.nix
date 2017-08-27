{ bash, jq, mkBin, utillinux }:

mkBin {
  name   = "hsNameVersion";
  paths  = [ bash jq utillinux ];
  script = ''
    #!/usr/bin/env bash

    # Takes a string containing a Haskell package name, returns JSON with
    # the version (if found) and the package name (with version stripped, if
    # given)

    if echo "$1" | grep -- "-[0-9][0-9.]*$" > /dev/null
    then
      # We have a version number in our package field; split it up
         NAME=$(echo "$1" | rev | cut -d '-' -f 2- | rev)
      VERSION=$(echo "$1" | rev | cut -d '-' -f 1  | rev)

      jq -n --arg name "$NAME"       \
            --arg version "$VERSION" \
            '{"package":$name,"version":$version}'
    else
      # We don't have a version number in our package field; leave as-is
      jq -n --arg name "$1" '{"package":$name}'
    fi
  '';
}
