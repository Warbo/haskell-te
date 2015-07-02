#!/usr/bin/env bash

# Runs AstPlugin, assuming there's a Cabal project in the current directory and
# that all of its dependencies are available (eg. thanks to nix-shell)

function getName {
    cut -d ':' -f 2
}

function arityCount {
    # This function serves two roles:
    #  - Echo the arity of a Haskell function type (how many non-nested "->")
    #  - Echo the return type of a Haskell function type
    #
    # To get the first behaviour, set $3 to 0. To get the second behaviour, set
    # $3 to the result of the first behaviour, ie:
    #
    # ARITY=$( arityCount "Bool -> (Int -> String) -> Float" 0 0)
    # RESULT=$(arityCount "Bool -> (Int -> String) -> Float" 0 $ARITY)
    #
    # In this example, $ARITY should be 2 and $RESULT should be "Float"
    #
    # $1 is the type, eg. "Bool -> (Int -> String) -> Float"
    # $2 counts how nested we are; it should always start at 0
    # $3 is a "countdown" of how many arrows are left until the return type
    case "$1" in
        "("*)
            STR=$(echo "$1" | cut -c 2-)
            arityCount "$STR" $(( $2 + 1 )) $3
            ;;
        ")"*)
            STR=$(echo "$1" | cut -c 2-)
            arityCount "$STR" $(( $2 - 1 )) $3
            ;;
        "->"*)
            if [[ "$2" -eq 0 ]]
            then
                if [[ $3 -eq 1 ]]
                then
                    # We've hit the last argument; echo it
                    echo "$1" | cut -c 3- | grep -o "[^ ].*"
                elif [[ $3 -gt 1 ]]
                then
                    # Decrease our countdown
                    STR=$(echo "$1" | cut -c 3-)
                    arityCount "$STR" $2 $(( $3 - 1 ))
                else
                    # Increament our counter
                    STR=$(echo "$1" | cut -c 3-)
                    REST=$(arityCount "$STR" $2 $3)
                    echo $(( $REST + 1 ))
                fi
            else
                # Ignore nested "->"
                STR=$(echo "$1" | cut -c 3-)
                arityCount "$STR" $2 $3
            fi
            ;;
        "")
            echo 0
            ;;
        *)
            STR=$(echo "$1" | cut -c 2-)
            arityCount "$STR" $2 $3
            ;;
    esac
}

function returnType {
    ARITY=$(arityCount "$1" 0 0)
    if [[ "$ARITY" -eq 0 ]]
    then
        # Constant
        echo "$1"
    else
        # Function; get the return type
        arityCount "$1" 0 "$ARITY"
    fi
}

function ghcPkg {
    # Get the Haskell package database, since we'll probably need to override GHC's
    # default choice. The first line of `ghc-pkg list` will tell us, except for a
    # pesky ':' at the end of the line
    ghc-pkg list | head -n 1 | tr -d ':'
}

function buildWithPlugin {
    # Tell GHC to use the right package database, to expose the AstPlugin package,
    # and to run the AstPlugin.Plugin during compilation
    GHC_PKG=$(ghcPkg)
    PLUGIN="AstPlugin.Plugin"
    OPTIONS="-package-db=$GHC_PKG -package AstPlugin -fplugin=$PLUGIN"

    # Build the project using Cabal, passing the above options through to GHC.
    # NOTE: AstPlugin writes to stderr, not stdout, so we redirect it (blame GHC!)
    cabal --ghc-options="$OPTIONS" build 2>&1 1>/dev/null
}

function getAsts {
    while read RAWLINE
    do
        # See if we're dealing with an AST or something else
        if echo "$RAWLINE" | grep "^FOUNDAST " > /dev/null
        then
            # Skip explicit dictionary-passing introduced by Core
            if echo "$RAWLINE" | grep '\.\$' > /dev/null
            then
                true
            else
                # Trim off the "FOUNDAST " prefix
                echo "$RAWLINE" | cut -d ' ' -f 2-
            fi
        else
            # Since these lines came from stderr, we might as well
            # report them
            echo "$RAWLINE" > /dev/stderr
        fi
    done
}

function typeCommand {
    # Since we have all of the required dependencies available, we can try
    # getting the types too. This will encounter errors, eg. for non-exported
    # names, but that's a feature: if we can't use them from here, then
    # QuickSpec can't later on either!
    # TODO: In the future, we might try looping through all of the executables,
    # test suites, etc. to make sure we cover as much as possible.

    # Build one big type-printing command, to avoid GHCi setup/teardown overhead
    # The ":m" unloads everything except Prelude, ensuring that names all get
    # qualified and we can't see any non-exported members
    echo ":m"
    getName | while read NAME
              do
                  # Make a GHCi command to print the type
                  echo ":t (${NAME})"
              done
}

function cabalLines {
    # Run the command through GHCi and concatenate any responses which spill
    # over multiple lines
    cabal repl | while read LINE
                 do
                     if echo "$LINE" | grep '^Prelude>' > /dev/null
                     then
                         printf "\n${LINE}"
                     else
                         printf " ${LINE}"
                     fi
                 done
}

function getTypes {
    # Extract any types we were given by GHCi
    cut -d '>' -f 2- | grep " :: "
}

function getReturnTypes {
    # QuickSpec requires all return values to implement Ord, so get them
    grep -o '::.*' | grep -o "[^ ].*" | while read TYPE
                                        do
                                            returnType "$TYPE"
                                        done
}

function isOrdCmd {
    # Try to partially-apply ">" to each value, to see if it admits an instance
    # of Ord
    echo ":m"
    while read NAME
    do
        echo ":t ((${NAME}) >)"
    done
}

function getTypeInfo {
    getReturnTypes | sort -u | typeInfoCmd | cabal repl
}

function onlyOrd {
    TYPES=$(cat)
    ORDS=$(echo "$TYPES" | getTypeInfo | grep "instance Ord")
    echo "$TYPES" | while read TYPE
                    do
                        RET=$(returnType "$TYPE")
                        if echo "$ORDS" | grep "$RET" > /dev/null
                        then
                            echo "$TYPE"
                        fi
                    done
}

echo " (Data.Bool.||) :: Bool -> Bool -> Bool
 (Data.Bool.not) :: Bool -> Bool" | getTypeInfo

exit 0

UNTYPED=$(buildWithPlugin)
ASTS=$(    echo "$UNTYPED"  | getAsts)
CMD=$(     echo "$ASTS"     | typeCommand)
RESPONSE=$(echo "$CMD"      | cabalLines)
TYPES=$(   echo "$RESPONSE" | getTypes)
ORDS=$(    echo "$TYPES"    | getOrds)


# Print out all ASTs which have a corresponding type
echo "$ASTS" | while read LINE
               do
                   NAME=$(echo "$LINE" | cut -d ' ' -f 1)
                   AST=$(echo "$LINE" | cut -d ' ' -f 2-)
                   QNAME=$(echo "$NAME" | cut -d ':' -f 2-)
                   TYPE=$(echo "$TYPES" | grep "(${QNAME}) ::" |
                              grep -o ": .*" |
                              grep -o "[^ :].*")
                   if [ -n "$TYPE" ]
                   then
                       echo "${NAME}:\"${TYPE}\" ${AST}"
                   fi
               done
