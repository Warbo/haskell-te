#!/usr/bin/env bash

BASE=$(dirname "$(readlink -f "$0")")

FILES="$*"
[[ -n "$FILES" ]] || FILES="$BASE"/benchmarks/*.smt2

echo "Going to benchmark '$FILES'" 1>&2

for F in $FILES
do
    NAME=$(basename "$F" .smt2)

    echo "Benchmarking '$F' with mlspec" 1>&2

    for N in 1 2 3 4
    do
        nix-shell -p "(import \"\${$BASE}/release.nix\").package" --run \
          "DO_BENCH=1 CLUSTERS=$N mlspecBench < '$F' 1> '$NAME-mlspec-$N.stdout' 2> '$NAME-mlspec-$N.stderr'"
    done

    echo "Benchmarking '$F' with quickspec" 1>&2

    nix-shell -p "(import \"\${$BASE}/release.nix\").package" --run \
      "DO_BENCH=1 quickspecBench < '$F' 1> '$NAME-quickspec-$N.stdout' 2> '$NAME-quickspec-$N.stderr'"
done
