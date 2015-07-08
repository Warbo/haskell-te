grep 'Test\.QuickSpec\.fun. ""' |
    while IFS= read -r LINE
    do
        RNAME=$(echo "$LINE"                |
                       grep -o '"[ ]*(.*)[ ]*::'  |
                       grep -o '(.*)'       |
                       grep -o '[^(].*[^)]' |
                       rev)
        NAME=$(echo "$RNAME" | cut -d '.' -f 1  | rev)
        MODS=$(echo "$RNAME" | cut -d '.' -f 2- | rev)

        ARITY=$(echo "$LINE"                                 |
                       grep -o 'Test\.QuickSpec\.fun[0-9] "' |
                       grep -o '[0-9]')

        echo "{\"module\": \"$MODS\", \"name\": \"$NAME\", \"arity\": \"$ARITY\"}"
    done | jq -s '.'
