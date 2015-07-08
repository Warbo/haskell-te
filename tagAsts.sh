function tagArity {
    # Select matching ASTs
    QUERY='select((.module == $given.m) and (.name == $given.n))'

    # Append the arity
    ACTION='. + {arity: $given.a}'

    # Our arguments are the qualified name and the arity
    NAME=$(echo "$1" | rev | cut -d '.' -f 1  | rev)
    MODS=$(echo "$1" | rev | cut -d '.' -f 2- | rev)
    GIVEN="{\"m\": \"$MODS\", \"n\": \"$NAME\", \"a\": $2}"

    getTypes | getTyped | jq -c --argfile given <(echo "$GIVEN") \
                             "$QUERY | $ACTION"
}

function tagType {
    # Select matching ASTs
    QUERY='select((.module == $given.m) and (.name == $given.n))'

    # Append the type
    ACTION='. + {type: $given.t}'

    # Our arguments are the module, name and type
    GIVEN="{\"m\": \"$1\", \"n\": \"$2\", \"t\": \"$3\"}"

    getAsts | jq -c --argfile given <(echo "$GIVEN") \
                 "$QUERY | $ACTION"
}
