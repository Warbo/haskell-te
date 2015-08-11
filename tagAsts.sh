#!/usr/bin/env bash

# Given JSON objects on stdin, and a file descriptor containing JSON objects as
# as $1, returns the intersection of the two

# Call the current AST $this, then loop over $tags
INPUT='.[] | . as $this | $tags | .[]'

# Select $tags matching $this
QUERY='select((.module == $this.module) and (.name == $this.name))'

# Combine matching $tags with $this
ACTION='. + $this'

jq --argfile tags "$1" "[$INPUT | $QUERY | $ACTION]"
