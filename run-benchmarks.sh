#!/usr/bin/env bash

BASE=$(dirname "$(readlink -f "$0")")

for F in $*
do
    NAME=$(basename "$F" .smt2)

    for N in 1 2 3 4
    do
        nix-shell -p "(import \"\${$BASE}/release.nix\").package" --run \
          "DO_BENCH=1 CLUSTERS=$N mlspecBench < '$F' 1> '$NAME-mlspec-$N.stdout' 2> '$NAME-mlspec-$N.stderr'"
    done

    nix-shell -p "(import \"\${$BASE}/release.nix\").package" --run \
      "DO_BENCH=1 quickspecBench < '$F' 1> '$NAME-quickspec-$N.stdout' 2> '$NAME-quickspec-$N.stderr'"
done
