{ benchmark, parseJSON, recurrent-clustering, runScript, withNix }:
with builtins;

{ quick, annotated, clusters }:

let go = c: parseJSON (runScript (withNix {
                                  buildInputs = [ recurrent-clustering ];
                                }) ''
             set -e
             export CLUSTERS="${toString c}"
             "${benchmark quick "cluster" []}" < "${annotated}" > "$out"
           '');
 in listToAttrs (map (c: { name  = toString c;
                           value = go c; })
                     clusters)
