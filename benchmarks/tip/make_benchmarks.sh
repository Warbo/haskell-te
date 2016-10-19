#!/usr/bin/env bash

function allNames {
    nix-shell -p '(import ./nix-support {}).tipBenchmarks.te-benchmark' \
              --run "all_names.rkt" < "$TIP" | tr ' ' '\n' | grep -v '^par$'
}

function tipNamesToHaskell {
    tr -d '_/.'
}

function wrapNames {
    OBJ='{"name": ., "package": "tip-benchmark-sig", "module": "A"}'
    tipNamesToHaskell | nix-shell -p jq --run "jq -R '$OBJ' | jq -s '.'"
}

[[ -e benchmarks/tip/make_benchmarks.sh ]] || {
    echo "$0 should be run from the top-level haskell-te directory" 1>&2
    exit 1
}

# Generate an smtlib file of all functions
TIP=$(nix-build --show-trace --no-out-link -E \
                '(import ./nix-support {}).tipBenchmarks.tip-benchmark-smtlib')

NAMES=$(allNames)

# Loop through each sample size we care about
for SIZE in 1 10 20 30 40 50
do
    printf 'Sampling for %s' "$SIZE"
    # Take 10 samples of this size
    for _ in $(seq 1 10)
    do
        # Select SIZE function names from the combined benchmarks
        SAMPLE=$(echo "$NAMES" | shuf | head -n$SIZE | wrapNames)
        SHA=$(echo "$SAMPLE" | sort | sha256sum | grep -o '^[^ ]*')
        echo "$SAMPLE" > "benchmarks/tip/sample-$SIZE-$SHA.json"
        printf '.'
    done
    printf '\n'
done
