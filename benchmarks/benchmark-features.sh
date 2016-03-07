#!/usr/bin/env bash
BASE=$(dirname "$(dirname "$(readlink -f "$0")")")

"$BASE/benchmarks/benchmark-dump-asts.sh" "$@" || {
    echo "benchmark-dump-asts.sh failed" >> /dev/stderr
    exit 1
}

"$BASE/benchmarks/benchmark-annotate.sh"  "$@" || {
    echo "benchmark-annotate.sh failed" >> /dev/stderr
    exit 1
}

exit 0
