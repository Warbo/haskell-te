{ benchmark, lib, ml4hs, parseJSON, runScript, withNix }:
with lib;

{ quick, clustered }:

let go = c: data: parseJSON (runScript (withNix {
                                         buildInputs = [ ml4hs ];
                                       }) ''
      set -e
      export CLUSTERS="${c}"
      "${benchmark quick "${ml4hs}/lib/ml4hs/ml4hs.sh" []}" < "${data}" \
                                                            > "$out"
    '');
 in mapAttrs go clustered
