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

# How far to go, to allow testing intermediate results
PHASE="$1"

function typeCommand {
    getAsts | ML4HSHelper "typeCommand"
}

function ordCommand {
    getTypes | ML4HSHelper "ordCommand"
}

function cabalLines {
    # Clean up GHCi output
    while read LINE
    do
        if echo "$LINE" | grep '^Prelude>' > /dev/null
        then
            printf "\n${LINE}"
        else
            printf " ${LINE}"
        fi
    done | grep " :: "          |
           sed 's/Prelude>//g'  |
           sed 's/\*[^ >]*>//g' |
           grep -o "([^)]*) :: .*"
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

function renderAll {
    # S-exprs for Haskell to read
    getAsts
    getTypes | while read LINE
               do
                   NAME=$(getName "$")
                   if getOrdResults | grep "(${NAME}).*::" > /dev/null
                   then
                       TYPE=$(getType "$NAME")
                       echo "(\"::\" \"$NAME\" \"${TYPE}\")"
                   fi
               done
}

function finalLines {
    renderAll | ML4HSHelper "renderAsts"
}

# Cache the results of running Cabal and GHC
PKGCACHE=""
BUILDCACHE=""
TYPECACHE=""
ORDCACHE=""

function ghcPkg {
    echo "$PKGCACHE" | head -n 1 | tr -d ':'
}

function ghcPkgFill {
    # Get a Haskell package database containing project dependencies and plugin
    PKGCACHE=$(ghc-pkg list)
}

function getAsts {
    PKG=$(pkgName)
    echo "$BUILDCACHE" | grep "^{" | jq -c ". + {package: \"$PKG\"}"
}

function buildWithPluginFill {
    # Override pkg db to get project's dependencies and AstPlugin
    GHC_PKG=$(ghcPkg)
    OPTIONS="-package-db=$GHC_PKG -package AstPlugin -fplugin=AstPlugin.Plugin"

    # NOTE: GHC plugins write to stderr!
    BUILDCACHE=$(cabal --ghc-options="$OPTIONS" build 2>&1 1>/dev/null)
}

function getTypes {
    echo "$TYPECACHE" | cabalLines
}

function getTypesFill {
    TYPECACHE=$(typeCommand | cabal repl)
}

function getOrdResults {
    echo "$ORDCACHE" | cabalLines
}

function getOrdResultsFill {
    ORDCACHE=$(ordCommand | cabal repl)
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

ghcPkgFill
buildWithPluginFill

getAsts     | phaseDump asts    && exit
typeCommand | phaseDump typeCmd && exit

getTypesFill

getTypes   | phaseDump types  && exit
ordCommand | phaseDump ordCmd && exit

getOrdResultsFill

getOrdResults | phaseDump ords   && exit
renderAll     | phaseDump render && exit

finalLines
