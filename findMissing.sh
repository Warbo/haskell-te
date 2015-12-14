#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq bash

INPUT=$(cat)

function skip {
    echo "$1" | grep '^\$[a-z]' > /dev/null && return 0
    echo "$1" | grep '^[A-Z]'   > /dev/null && return 0
    return 1
}

while read -r ENTRY
do
    while read -r DEP
    do
        NAME=$(echo "$DEP" | jq -r '.name')
        MOD=$( echo "$DEP" | jq -r '.module')
        PKG=$( echo "$DEP" | jq -r '.package')

        skip "$NAME" && continue

        FOUND=$(echo "$INPUT" |
            jq -c --arg name "$NAME" \
                  --arg mod  "$MOD"  \
                  --arg pkg "$PKG"   \
                  'map(select(.name == $name and .module == $mod and .package == $pkg)) | length')

        [[ "$FOUND" -gt 1 ]] && {
            echo "WARNING: Found multiple entries for '$DEP'"
        }
        [[ "$FOUND" -eq 0 ]] && {
            echo "WARNING: No entry for '$DEP'"
        }
    done < <(echo "$ENTRY" | jq -c '.dependencies | .[]')
done < <(echo "$INPUT" | jq -c '.[]')
