#!/bin/sh

# Extract ASTs from the Cabal package in the current directory

function packageName {
    (shopt -s nullglob
     for CBL in *.cabal
     do
         grep "name:" < "$CBL" | cut -d ':' -f 2 | tr -d '[:space:]'
     done)
}

function extractAsts {
    PKG=$(packageName)
    nix-shell -E "with import <nixpkgs> {}; ghcWithPlugin \"$PKG\"" \
              --run "sh" <<'EOF'
# Get this shell's Haskell package database. The first line of `ghc-pkg list`
# will tell us, except for a pesky ':' at the end of the line
GHC_PKG=$(ghc-pkg list | head -n 1 | tr -d ':')

# Tell GHC to use the right package database, to expose the AstPlugin package,
# and to run the AstPlugin.Plugin during compilation
PLUGIN="AstPlugin.Plugin"
OPTIONS="-package-db=$GHC_PKG -package AstPlugin -fplugin=$PLUGIN"

# Build the project, passing the above options through to GHC.
# NOTE: AstPlugin writes to stderr, not stdout, so we redirect it (blame GHC!)
cabal --ghc-options="$OPTIONS" build 2>&1 1>/dev/null
EOF
}

extractAsts | grep "^FOUNDAST" | cut -d ' ' -f 2-
