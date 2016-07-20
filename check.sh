#!/usr/bin/env bash

#nix-instantiate --show-trace ./release.nix

NIX_PATH="$PWD:$NIX_PATH" nix-build --option restrict-eval true --show-trace -A tests release.nix
