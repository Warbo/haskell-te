#!/usr/bin/env bash

# Runs AstPlugin.
#
# This script makes the following assumptions:
#  - The current working directory contains a Cabal project
#  - All of the project's dependencies are in the database of ghc-pkg
#  - AstPlugin is also in the database of ghc-pkg

# All of these requirements can be satisfied by running in nix-shell

set -e

function getAsts {
    RESULT=$(build)
    { echo "$RESULT" | grep -v "^{" > /dev/stderr; } || true
      echo "$RESULT" | grep    "^{"
}

function build {
    # Override pkg db to get project's dependencies and AstPlugin
    GHC_PKG=$(ghc-pkg list | head -n 1 | tr -d ':')
    OPTIONS="-package-db=$GHC_PKG -package AstPlugin -fplugin=AstPlugin.Plugin"
    # NOTE: GHC plugins write to stderr!
    cabal --ghc-options="$OPTIONS" build 1>/dev/null 2>&1
}

cabal configure > /dev/stderr
getAsts
