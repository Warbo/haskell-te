defs: with defs;

testRun "Can build package" null { buildInputs = [ package ]; } "exit 0"
