#!/bin/sh

# Use cabal2nix to give every Cabal project a Nix file
# We run the loop inside nix-shell to save setup/teardown time
PROJECTS=$(cat)
nix-shell -p cabal2nix --run "sh" <<EOF
echo "$PROJECTS" | while read PROJECT
                   do
                       (cd "\$PROJECT"; cabal2nix --shell ./. > shell.nix)
                   done
EOF
