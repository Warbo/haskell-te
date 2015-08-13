#!/usr/bin/env bash

source common.sh

function runProject {
    (cd "$1"; nix-shell --run "cabal configure" && cabal run)
}

while read PROJECT
do
    runProject "$PROJECT"
done
