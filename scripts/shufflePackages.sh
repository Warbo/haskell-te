#!/usr/bin/env bash
BASE=$(dirname "$(dirname "$(readlink -f "$0")")")
source "$BASE/scripts/common.sh"

info "Ensuring we have a Hackage list"
if [[ -n "$1" ]]
then
    F="$1"
elif [[ -f "$CACHE/index.tar.gz" ]]
then
    F="$CACHE/index.tar.gz"
else
    URL="http://hackage.haskell.org/packages/index.tar.gz"
    info "Downloading Hackage package list from '$URL'"
    wget -O "$CACHE/index.tar.gz" "$URL" ||
        abort "Failed to fetch package list"
fi

info "Checking for shuffled package list"
CACHE="$CACHE/shuffled"
if [[ -f "$CACHE" ]]
then
    info "Using cached packages '$CACHE'"
    cat "$CACHE"
    exit 0
fi
info "Generating new shuffled list"

function extractVersions {
    PKG=""
    LATEST=""
    while read -r LINE
    do
        THIS_PKG=$(echo "$LINE" | cut -d / -f 1)
        if ! [[ "x$PKG" = "x$THIS_PKG" ]]
        then
            # Reached a new package; report the latest version of the last one
            [[ -z "$PKG" ]] || echo -e "$PKG\t$LATEST"

            # Start tracking this package instead
            PKG="$THIS_PKG"
        fi

        # Bump the latest version we've seen
        LATEST=$(echo "$LINE" | cut -d / -f 2)
    done < <(tar -ztf "$F" | grep -o '[^/][^/]*/[0-9][^/]*')
    echo -e "$PKG\t$LATEST"
}

function withVersions {
    HASH=$(md5sum "$F" | cut -d ' ' -f 1)
    CACHED="$CACHE/package-versions-$HASH"
    if [[ -f "$CACHED" ]]
    then
        cat "$CACHED"
    else
        info "Caching package versions to '$CACHED'"
        extractVersions | tee "$CACHED"
    fi
}

function randomPkgs {
    withVersions | uniq | shuf
}

randomPkgs | tee "$CACHE"
