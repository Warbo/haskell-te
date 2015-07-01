#!/bin/sh

TOP="$1"

function getDirs {
    (shopt -s nullglob;
     for ENTRY in "$TOP/"*
     do
         if [ -d "$ENTRY" ]
         then
             readlink -f "$ENTRY"
         fi
     done)
}

function makeNix {
    PROJECTS=$(cat)
    nix-shell -p cabal2nix --run "sh" <<EOF
echo "$PROJECTS" | while read PROJECT
                   do
                       (cd "\$PROJECT"; cabal2nix --shell ./. > shell.nix)
                   done
EOF
}

function makeAllNix {
    getDirs | makeNix
}

function runProject {
    (cd "$1"; nix-shell --run "cabal configure" && cabal run)
}

function runAllProjects {
    getDirs | while read PROJECT
              do
                  runProject "$PROJECT"
              done
}

makeAllNix

runAllProjects
