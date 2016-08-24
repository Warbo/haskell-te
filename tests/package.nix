defs: with defs;

testRun "Can build package" null { buildInputs = [ (import ./..) ]; } "exit 0"
