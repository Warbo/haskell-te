#!/usr/bin/env bash
BASE=$(dirname "$(dirname "$(readlink -f "$0")")")

"$BASE/benchmarks/benchmark-dump-asts.sh" "$@" &&
"$BASE/benchmarks/benchmark-annotate.sh"  "$@"
