#!/usr/bin/env bash
if [[ -n "$1" ]]
then
    F="$1"
else
    F="index.tar.gz"
fi

function randomNames {
    tar -ztf "$F" | cut -d / -f 1 | sort -u | shuf
}

function version {
    tar -ztf "$F" | grep "^$1/" | tail -n1 | cut -d / -f 1-2 | tr / -
}

function withVersions {
    while read -r PKG
    do
        version "$PKG"
    done < <(randomNames)
}

withVersions
