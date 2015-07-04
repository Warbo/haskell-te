#!/bin/sh

# Extract ASTs from a Cabal package

BASE=$(dirname "$0")

DIR="$PWD"
if [[ "$#" -gt 0 ]]
then
    DIR="$1"
fi

function packageName {
    (shopt -s nullglob
     for CBL in "$DIR"/*.cabal
     do
         grep "name:" < "$CBL" | cut -d ':' -f 2 | tr -d '[:space:]'
     done)
}

function extractAsts {
    PKG=$(packageName)
    (cd "$DIR";
     nix-shell -E "with import <nixpkgs> {}; ghcWithPlugin \"$PKG\"" \
               --run "$BASE/runPlugin.sh")
}

function fixPackageName {
    # FIXME: This is a hack. AstPlugin should get the package name and include
    # it in the output, but we seem to get "(unknown):Foo.bar (ast)".
    # The easy workaround is to replace "(unknown)" with the given package name.
    # Longer-term, it would be better to fix this in AstPlugin itself.
    PKG=$(packageName)
    cut -d ':' -f 2- | while read LINE
                       do
                           echo "$PKG:$LINE"
                       done
}

extractAsts | fixPackageName
