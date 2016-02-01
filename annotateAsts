#! /usr/bin/env nix-shell
#! nix-shell -p jq -i bash

set -e

INPUT=$(cat)
RAWASTS=$(echo  "$INPUT" | jq -c '.asts')
RAWTYPES=$(echo "$INPUT" | jq -r '.result')
RAWSCOPE=$(echo "$INPUT" | jq -r '.scoperesult')

echo "$RAWASTS" |
    ./tagAsts.sh <(echo "$RAWSCOPE" | ./getTypes.sh)   |
    ./tagAsts.sh <(echo "$RAWTYPES" | ./getArities.sh)
