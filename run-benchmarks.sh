#!/usr/bin/env bash

BASE=$(dirname "$(readlink -f "$0")")
# shellcheck source=scripts/common.sh
source "$BASE/scripts/common.sh"

requireCmd nix-env

NIX_PATH="$("$BASE/nix-support/nixPath.sh")"
export NIX_PATH

# Create a new Nix profile and install haskell-te-env into it
nix-env -f "$BASE/nix-support/defexpr" \
        -p "$CACHE/haskell-te-env" \
        -iA haskell-te || abort "Failed to set up haskell-te-env"

PATH="$CACHE/haskell-te-env/bin" "$BASE/benchmarks/benchmark.sh"
