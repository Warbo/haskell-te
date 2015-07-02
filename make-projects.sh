#!/bin/sh

nix-shell -p mlspec --run "MLSpec $1" | grep "^PROJECT" | cut -d ' ' -f 2-
