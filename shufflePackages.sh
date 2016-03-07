#!/usr/bin/env bash
BASE=$(dirname "$(readlink -f "$0")")
DIR=$("$BASE/cacheDir.sh")
if [[ -n "$1" ]]
then
    F="$1"
elif [[ -f "$DIR/index.tar.gz" ]]
then
    F="$DIR/index.tar.gz"
else
    URL="http://hackage.haskell.org/packages/index.tar.gz"
    echo "Downloading Hackage package list from '$URL'" >> /dev/stderr
    wget -O "$DIR/index.tar.gz" "$URL" || {
        echo "Failed to fetch package list, aborting" >> /dev/stderr
        exit 1
    }
fi

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
    CACHED="$DIR/package-versions-$HASH"
    if [[ -f "$CACHED" ]]
    then
        cat "$CACHED"
    else
        echo "Caching package versions to '$CACHED'" >> /dev/stderr
        extractVersions | tee "$CACHED"
    fi
}

function randomPkgs {
    withVersions | uniq | shuf
}

randomPkgs
