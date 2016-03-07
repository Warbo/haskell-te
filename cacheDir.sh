#!/usr/bin/env bash

function fail {
    echo "$0: FAIL: $1" >> /dev/stderr
    exit 1
}

BASE=$(dirname "$(readlink -f "$0")")
if [[ -w "$BASE" ]]
then
    # If we can write to the same place as our scripts, do so as it allows
    # committing files for reproducibility
    DIR="$BASE/cache"
    mkdir -p "$DIR" 1>&2 || fail "Couldn't create dir '$DIR'"
elif [[ -n "$XDG_CACHE_HOME" ]] && [[ -d "$XDG_CACHE_HOME" ]]
then
    # On many systems, 'mktemp -d' will use an in-memory filesystem, which will
    # quickly fill up. To avoid that, we try to use XDG_CACHE_HOME instead.
    DIR="$XDG_CACHE_HOME/haskell-te"
    mkdir -p "$DIR" 1>&2 || fail "Couldn't create dir '$DIR'"
elif [[ -n "$HOME" ]] && [[ -d "$HOME" ]]
then
    # If $HOME exists, try falling back to the recommended ~/.cache directory
    DIR="$HOME/.cache/haskell-te"
    mkdir -p "$DIR" 1>&2 || fail "Couldn't create dir '$DIR'"
else
    # If $HOME doesn't exist, we're probably a daemon. Use mktemp, in the hope
    # that it's sane.
    DIR=$(mktemp -d "haskell-te") || fail "Couldn't create temp dir $DIR"
fi

echo "Caching data in '$DIR'" >> /dev/stderr
echo "$DIR"
