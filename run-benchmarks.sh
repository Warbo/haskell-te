#!/usr/bin/env bash

BASE=$(dirname "$(readlink -f "$0")")

FILES="$*"
[[ -n "$FILES" ]] || FILES="$BASE"/benchmarks/*.smt2

echo "Going to benchmark '$FILES'" 1>&2

for F in $FILES
do
    NAME=$(basename "$F" .smt2)

    for N in 1 2 3 4
    do
        OUT="$NAME-mlspec-$N.stdout"
        if ! [[ -e "$OUT" ]]
        then
            echo "Benchmarking '$F' with '$N' mlspec clusters" 1>&2
            nix-shell -p "(import \"\${$BASE}/release.nix\").package" --run \
              "DO_BENCH=1 CLUSTERS=$N mlspecBench < '$F' 1> '$OUT' 2> '$NAME-mlspec-$N.stderr'"
        fi
    done

    OUT="$NAME-quickspec.stdout"
    if ! [[ -e "$OUT" ]]
    then
        echo "Benchmarking '$F' with quickspec" 1>&2
        nix-shell -p "(import \"\${$BASE}/release.nix\").package" --run \
          "DO_BENCH=1 quickspecBench < '$F' 1> '$OUT' 2> '$NAME-quickspec.stderr'"
    fi
done
