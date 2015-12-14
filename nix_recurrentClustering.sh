#!/usr/bin/env bash

# nix-shell shebangs don't like whitespace, so we call nix-shell explicitly
nix-shell -p 'import ./weka-cli.nix' jq bash order-deps perl \
          --run "./recurrentClustering.sh"
