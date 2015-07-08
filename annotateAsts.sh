#! /usr/bin/env nix-shell
#! nix-shell -p jq -i bash

set -e

INPUT=$(cat)
RAWASTS=$(echo  "$INPUT" | jq -c '.asts')
RAWTYPES=$(echo "$INPUT" | jq -r '.result')

echo "$RAWASTS" |
    ./tagAsts.sh <(echo "$RAWTYPES" | ./getTypes.sh)   |
    ./tagAsts.sh <(echo "$RAWTYPES" | ./getArities.sh) |
    ./extractFeatures.sh
