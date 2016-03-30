#!/usr/bin/env bash
nix-instantiate --show-trace --eval -E 'import ./test.nix'
