#!/usr/bin/env bash

BASE=$(dirname "$(readlink -f "$0")")
"$BASE/scripts/readBenchJson.sh"
