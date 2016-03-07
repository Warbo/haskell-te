#!/usr/bin/env bash

# Benchmark regular building with Cabal + GHC

[[ -n "$1" ]] || {
    echo "'$0' requires a package directory" >> /dev/stderr
    exit 1
}

[[ -d "$1" ]] || {
    echo "'$0': Directory '$1' not found" >> /dev/stderr
    exit 1
}

command -v cabal > /dev/null || {
    echo "'$0' requires cabal" >> /dev/stderr
    exit 1
}

cd "$1" || {
    echo "$0: Couldn't cd to '$1'" >> /dev/stderr
    exit 1
}

echo "'$0' not implemented"; exit 1

nix-shell -E "$(cabal2nix --shell ./.)" --run "cabal configure"
benchmark cabal build
