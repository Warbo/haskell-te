#!/usr/bin/env bash

# The number of different cluster parameters to use
BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
"$BASE/scripts/clusterNums.sh" | wc -l
