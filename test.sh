#!/usr/bin/env bash
set -e

if nix-build -k --show-trace
then
    echo     "ok - Build finished gracefully"
else
    echo "not ok - Build finished gracefully"
    exit 1
fi
