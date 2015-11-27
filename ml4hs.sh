#! /usr/bin/env nix-shell
#! nix-shell -p jq -p bash -i bash
set -e

# Main ML4HS script

# Check invocation

if [ "$#" -lt 1 ]
then
    echo "Please provide a Haskell project name"
    exit 1
fi

./dump-hackage.sh "$1"   |
./runTypes.sh     "$1"   |
./annotateAsts.sh        |
./cluster.sh             |
./run-exploration.sh
