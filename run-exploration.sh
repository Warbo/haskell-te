#!/usr/bin/env bash
source common.sh

nix-shell --show-trace -p mlspec --run "MLSpec"
