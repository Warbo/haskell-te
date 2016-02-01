#!/usr/bin/env bash

BASE_=$(dirname "$0")
BASE=$(readlink -f "$BASE_")

if [[ -e "$BASE/weka-cli.nix" ]]
then
    WEKACLI="$BASE/weka-cli.nix"
elif [[ -e "$BASE/../lib/weka-cli.nix" ]]
then
    WEKACLI="$BASE/../lib/weka-cli.nix"
else
    echo "Cannot find weka-cli.nix in '$BASE' or '$BASE/../lib/'" >> /dev/stderr
    exit 1
fi

# nix-shell shebangs don't like whitespace, so we call nix-shell explicitly
nix-shell -p "import \"$WEKACLI\"" jq bash order-deps perl \
          --run "$BASE/recurrentClustering"
