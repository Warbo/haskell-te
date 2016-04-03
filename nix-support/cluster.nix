{ benchmark, parseJSON, recurrent-clustering, runScript, withNix }:

{ quick, annotated, clusters }:

let go = c: parseJSON (runScript (withNix {
                                  buildInputs = [ recurrent-clustering ];
                                }) ''
             set -e
             export CLUSTERS="${builtins.toString c}"
             "${benchmark quick "cluster" []}" < "${annotated}" > "$out"
           '');
 in map (c: go c // { clusters = c; }) clusters
