function getArities {
    getTypes                             |
        grep 'Test\.QuickSpec\.fun. ""' |
        while IFS= read -r LINE
        do
            NAME=$(echo "$LINE" |
                          grep -o '" (.*) ::' |
                          grep -o '(.*)'      |
                          grep -o '[^(].*[^)]')
            ARITY=$(echo "$LINE"                                 |
                           grep -o 'Test\.QuickSpec\.fun[0-9] "' |
                           grep -o '[0-9]')
            tagArity "$NAME" "$ARITY"
        done
}
