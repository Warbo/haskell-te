#!/bin/sh

function packageName {
    (shopt -s nullglob
     for CBL in *.cabal
     do
         grep "name:" < "$CBL" | cut -d ':' -f 2 | tr -d '[:space:]'
     done)
}

PKG=$(packageName)
nix-shell -E "with import <nixpkgs> {}; ghcWithPlugin \"$PKG\"" \
          --run "sh" <<'EOF'
GHC_PKG=$(ghc-pkg list | head -n 1 | tr -d ':')
PLUGIN="AstPlugin.Plugin"
OPTIONS="-package-db=$GHC_PKG -package AstPlugin -fplugin=$PLUGIN"
echo "$OPTIONS"
cabal --ghc-options="$OPTIONS" build
EOF
