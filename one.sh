#!/bin/sh

nix-shell -p "with import <nixpkgs> {}; (callPackage ./. {}).$1" \
          --command 'true' --show-trace
