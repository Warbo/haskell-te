#!/usr/bin/env bash

BASE=$(dirname "$(dirname "$(readlink -f "$0")")")

# Get the path to 'nixpkgs'
REAL=$(nix-instantiate --eval -E '<nixpkgs>') || {
    echo "$0: Couldn't invoke Nix" >> /dev/stderr
    exit 1
}

# Alias <nixpkgs> to <real> and use ./nix-support in place of <nixpkgs>
[[ -d "$BASE/nix-support" ]] || {
    echo "$0: Couldn't find nix-support in '$BASE'" >> /dev/stderr
    exit 1
}

echo "nixpkgs=$BASE/nix-support:real=$REAL:$NIX_PATH"
