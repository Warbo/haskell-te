#!/usr/bin/env bash
set -e

if nix-build -k --show-trace "./nix-support/test.nix"
then
    echo     "ok - Test suite exited gracefully"
else
    echo "not ok - Test suite exited gracefully"
    exit 1
fi
