#!/usr/bin/env bash
source common.sh

nix-shell --show-trace -p mlspec --run "MLSpec $1" |
    grep "^PROJECT" |
    cut -d ' ' -f 2-
