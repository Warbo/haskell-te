#!/usr/bin/env bash

BASE=$(dirname "$(readlink -f "$0")")

# Get the path to 'nixpkgs'
REAL=$(nix-instantiate --eval -E '<nixpkgs>') || fail "Couldn't invoke Nix"

# Alias <nixpkgs> to <real> and use ./nix-support in place of <nixpkgs>
[[ -d "$BASE/nix-support" ]] || fail "Couldn't find nix-support in '$BASE'"
echo "nixpkgs=$BASE/nix-support:real=$REAL:$NIX_PATH"
