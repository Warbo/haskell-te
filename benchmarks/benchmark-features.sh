#!/usr/bin/env bash

echo "$0: not implemented yet" >> /dev/stderr

exit 1

cabal configure with AstPlugin
benchmark cabal build
benchmark annotatedb
