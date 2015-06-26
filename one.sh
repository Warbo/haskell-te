#!/bin/sh

nix-shell -p "(import ./. {}).$1" --command 'true' --show-trace
