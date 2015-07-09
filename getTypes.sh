#!/bin/sh

function trim {
    grep -o '[^ ].*[^ ]'
}

grep 'in f[ ]*::'                   |
    grep -o '([^)]*)) in f[ ]*::.*' |
    sed -e "s/::/\t/g"              |
    while read -r LINE
    do
        TERM=$(echo "$LINE" | cut -f 1 | trim)
        TYPE=$(echo "$LINE" | cut -f 2 | trim)

        # $TYPE is fine as-is; $TERM needs cutting down
        RNAME=$(echo "$TERM" | grep -o "('[^)]*)) in f" |
                               grep -o "'.*)) in "      |
                               cut -c 2-                |
                               rev | cut -c 7-)

        # Reverse 'Mod1.Mod2.name' to get 'eman.2doM.1doM', chop off the
        # first field, then reverse again to get 'Mod1.Mod2' and 'name'
        NAME=$(echo "$RNAME" | cut -d '.' -f 1  | rev)
        MODS=$(echo "$RNAME" | cut -d '.' -f 2- | rev)

        echo "{\"module\": \"$MODS\", \"name\": \"$NAME\", \"type\": \"$TYPE\"}"
    done | jq -s '.'
