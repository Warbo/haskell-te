#!/bin/sh

grep -v 'Test\.QuickSpec\.fun. ""'    |
    grep -o '([^)]*) ::.*'            |
    sed -e 's/(\([^)]*\)) :: /\1\t/g' |
    while read -r LINE
    do
        # Reverse 'Mod1.Mod2.name' to get 'eman.2doM.1doM', chop off the
        # first field, then reverse again to get 'Mod1.Mod2' and 'name'
        RNAME=$(echo "$LINE" | cut        -f 1  | rev)
        NAME=$(echo "$RNAME" | cut -d '.' -f 1  | rev)
        MODS=$(echo "$RNAME" | cut -d '.' -f 2- | rev)
        TYPE=$(echo "$LINE"  | cut        -f 2)
        echo "{\"module\": \"$MODS\", \"name\": \"$NAME\", \"type\": \"$TYPE\"}"
    done
