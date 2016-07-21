#!/usr/bin/env bash

NIX_PATH="$PWD:$NIX_PATH" nix-instantiate \
  --show-trace \
  --option restrict-eval true \
  release.nix
  #-A tests \

#NIX_PATH="$PWD:$NIX_PATH" nix-build --option restrict-eval true --show-trace -A tests release.nix
