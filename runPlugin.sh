#!/usr/bin/env bash

# Runs AstPlugin. This script makes the following assumptions:
#  - The current working directory contains a Cabal project
#  - All of the project's dependencies are in the database of ghc-pkg
#  - AstPlugin is also in the database of ghc-pkg
#  - The "ML4HSHelper" Haskell program is in $PATH

# All of these requirements can be satisfied by running in nix-shell

# Since we have the dependencies available, we also use GHCi to inspect types

set -e
set -x

function typeCommand {
    echo ":m"
    '"Test.QuickSpec.fun5 \"\" " + $qn'
    getAsts | while read -r LINE
              do
                  QNAME=$(echo "$LINE" | jq -r '.module + "." + .name')
                  echo ":t ($QNAME)"
                  mkQuery "$QNAME"
              done
}

function mkQuery {
    # Try making QuickSpec signatures
    for NUM in 5 4 3 2 1 0
    do
        printf ':t Test.QuickSpec.fun%d "" %s\n' "$NUM" "$1"
    done
}

function cabalLines {
    # Clean up GHCi output
    while IFS= read -r LINE
    do
        if echo "$LINE" | grep '^ ' > /dev/null
        then
            printf  " ${LINE}"
        else
            printf "\n${LINE}"
        fi
    done
}

function pkgName {
    for CABAL in *.cabal
    do
        grep "name:" < "$CABAL" | grep -o ":.*" | grep -o "[^: ].*"
        return
    done
}

function getName {
    # "(foo) :: Bar" => "foo"
    cut -d ':' -f 1 | grep -o "[^ (].*[^) ]"
}

function getType {
    # "(foo) :: Bar" => "Bar"
    grep -o "::.*" | grep -o "[^ :].*"
}

function getAsts {
    PKG=$(pkgName)
    echo "$BUILDCACHE" | grep "^{" | jq -c ". + {package: \"$PKG\"}"
}

function getTypes {
    echo "$TYPECACHE" | cabalLines
}

function getTyped {
    getTypes                              |
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
            tagType "$MODS" "$NAME" "$TYPE"
        done
}

function getArities {
    echo "$TYPECACHE" |
        cabalLines |
        grep -o
}

function tagType {
    # Select matching $asts
    QUERY='select((.module == $given.m) and (.name == $given.n))'

    # Append the type
    ACTION='. + {type: $given.t}'

    # Our arguments are the module, name and type
    GIVEN="{\"m\": \"$1\", \"n\": \"$2\", \"t\": \"$3\"}"

    getAsts | jq -c --argfile given <(echo "$GIVEN") \
                 "$QUERY | $ACTION"
}

function phaseDump {
    # If we've been asked for the given phase, dump stdin and exit success
    # (Since this is piped, it gets its own sub-shell, hence the exit)
    if [[ "x$PHASE" = "x$1" ]]
    then
        cat
        exit 0
    fi
    exit 1
}

# How far to go, to allow testing intermediate results
PHASE="$1"

BUILDCACHE=$(
    # Override pkg db to get project's dependencies and AstPlugin
    GHC_PKG=$(ghc-pkg list | head -n 1 | tr -d ':')
    OPTIONS="-package-db=$GHC_PKG -package AstPlugin -fplugin=AstPlugin.Plugin"
    # NOTE: GHC plugins write to stderr!
    cabal --ghc-options="$OPTIONS" build 2>&1 1>/dev/null)

getAsts     | phaseDump asts    && exit
typeCommand | phaseDump typeCmd && exit

TYPECACHE=$(typeCommand | cabal repl -v0)

echo "$TYPECACHE" | phaseDump typeCache && exit
getTypes          | phaseDump types  && exit
getTyped          | phaseDump typed  && exit
