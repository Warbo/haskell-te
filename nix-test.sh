#!/usr/bin/env bash
BASE=$(dirname "$(readlink -f "$0")")
NIX_PATH="$("$BASE/nix-support/nixPath.sh")" nix-instantiate \
    --read-write-mode --show-trace --eval -E 'import ./test.nix'
