#!/usr/bin/env bash
nix-instantiate --read-write-mode --show-trace --eval -E 'import ./test.nix'
