#!/usr/bin/env bash

command -v nix-shell > /dev/null || {
    echo "ERROR: nix-shell is needed for benchmarking" >> /dev/stderr
    exit 1
}

BASE=$(dirname "$(readlink -f "$0")")

NIX_PATH="$("$BASE/nix-support/nixPath.sh")" nix-shell --show-trace \
        --run "$BASE/benchmarks/benchmark.sh"
