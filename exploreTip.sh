#!/usr/bin/env bash

P=$(readlink -f "$1")

nix-instantiate --read-write-mode --show-trace --eval \
                -E "import ./nix-support/exploreTip.nix"
