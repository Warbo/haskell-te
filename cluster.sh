#!/usr/bin/env bash

source common.sh

# nix-shell shebangs don't like whitespace, so we call nix-shell explicitly
nix-shell -p 'import ./weka-cli.nix' jq bash --run "./runWeka.sh"
