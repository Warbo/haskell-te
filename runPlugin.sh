#!/usr/bin/env bash

# Runs AstPlugin.
#
# This script makes the following assumptions:
#  - The current working directory contains a Cabal project
#  - All of the project's dependencies are in the database of ghc-pkg
#  - AstPlugin is also in the database of ghc-pkg

# All of these requirements can be satisfied by running in nix-shell

set -e

function pkgName {
    # FIXME: Duplicated in dump-package.sh
    for CABAL in *.cabal
    do
        grep -i "name[ ]*:" < "$CABAL" | grep -o ":.*" | grep -o "[^: ].*"
        return
    done
}

function getAsts {
    PKG=$(pkgName)
    RESULT=$(build)
    echo "$RESULT" | grep -v "^{" > /dev/stderr
    echo "$RESULT" | grep    "^{" | jq -c ". + {package: \"$PKG\"}"
}

function build {
    # Override pkg db to get project's dependencies and AstPlugin
    GHC_PKG=$(ghc-pkg list | head -n 1 | tr -d ':')
    OPTIONS="-package-db=$GHC_PKG -package AstPlugin -fplugin=AstPlugin.Plugin"
    # NOTE: GHC plugins write to stderr!
    cabal --ghc-options="$OPTIONS" build 2>&1 1>/dev/null
}

getAsts | jq -s '.'
