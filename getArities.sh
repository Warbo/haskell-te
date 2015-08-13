#! /usr/bin/env nix-shell
#! nix-shell -i bash -p jq

source common.sh

# Split a qualified name into a module and a name
INPUT='(.qname | split(".") | reverse) as $bits'

# The name is the last bit
NAME='$bits[0]'

# The module is all except the last bit, joined by dots
MOD='$bits[1:] | reverse | join(".")'

grep '^{' |
    jq -c -M "$INPUT | . + {name: $NAME, module: $MOD} | del(.qname)" |
    jq -s -M '.'
