#! /usr/bin/env nix-shell
#! nix-shell -i bash -p bash order-deps jq

DEPS=$(cat)

OUTER='$ordered | .[] | .[] | . as $this'
INNER='$asts | .[]'
QUERY='select((.package == $this.package) and (.module == $this.module) and (.name == $this.name))'

jq -n -c --argfile asts    <(echo "$DEPS")              \
         --argfile ordered <(echo "$DEPS" | order-deps) \
         "$OUTER | $INNER | $QUERY" | jq -s '.'
