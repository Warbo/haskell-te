#! /usr/bin/env nix-shell
#! nix-shell -p jq -i bash

# Reduce an array of ASTs into an object {cluster1: [...], cluster2: [...], ...}
# Then convert that into an array of clusters (since the keys are meaningless)
jq 'reduce .[] as $ast ({}; .[$ast.cluster] += [$ast]) | .[]'
