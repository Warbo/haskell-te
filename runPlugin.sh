#!/usr/bin/env bash

# Runs AstPlugin, assuming there's a Cabal project in the current directory and
# that all of its dependencies are available (eg. thanks to nix-shell)

# Since we have the dependencies available, we also use GHCi to inspect types

function getAsts {
    # FIXME: What about newlines? We should probably just read every s-expr we
    # can (in Haskell) and filter out those without "FOUNDAST"
    buildWithPlugin | grep "FOUNDAST"
    #    while read RAWLINE
    #    do
    #        # Send non-AST lines back to stderr
    #        if ! echo "$RAWLINE" | grep "FOUNDAST"
    #        then
    #            echo "$RAWLINE" > /dev/stderr
    #        fi
    #    done
}

function typeCommand {
    getAsts | hs "typeCommand"
}

function ordCommand {
    getTypes | hs "ordCommand"
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

function getName {
    # "(foo) :: Bar" => "foo"
    cut -d ':' -f 1 | grep -o "[^ (].*[^) ]"
}

function getType {
    # "(foo) :: Bar" => "Bar"
    grep -o "::.*" | grep -o "[^ :].*"
}

function hs {
    # Use Haskell for any nontrivial text processing
    BASE=$(dirname "$0")
    "$BASE"/runPlugin.hs "$1"
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
    renderAll | hs "renderAsts"
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

function buildWithPlugin {
    echo "$BUILDCACHE"
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
    TYPECACHE=$(typeCommand | repl)
}

function getOrdResults {
    echo "$ORDCACHE" | cabalLines
}

function getOrdResultsFill {
    ORDCACHE=$(ordCommand | repl)
}

function repl {
    MACRO="dist/build/autogen/cabal_macros.h"
    if [ -e "$MACRO" ]
    then
        cabal --extra-include-dirs="$MACRO" repl
    else
        cabal repl
    fi
}

# Fill the caches
ghcPkgFill
buildWithPluginFill

getAsts
exit
getTypesFill
getOrdResultsFill

# Print out all ASTs with Ord instances
renderAll
#finalLines
