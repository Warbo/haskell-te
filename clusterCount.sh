#!/usr/bin/env bash

# The number of different cluster parameters to use
BASE=$(dirname "$(readlink -f "$0")")
"$BASE/clusterNums.sh" | wc -l
