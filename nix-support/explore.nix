{ benchmark, explore-theories, lib, ml4hs, parseJSON, runScript, withNix,
  writeScript }:
with lib;

{ quick, clustered }:

let formatAndExplore = writeScript "format-and-explore" ''
      set -e
      function noDepth {
        grep -v "^Depth" || true
      }

      "${ml4hs}/lib/ml4hs/format-exploration.sh" |
        explore-theories | noDepth
    '';
    go = c: data: parseJSON (runScript (withNix {
                                         buildInputs = [ explore-theories ml4hs ];
                                       }) ''
      set -e
      export CLUSTERS="${c}"
      "${benchmark quick "${formatAndExplore}" []}" < "${data}" \
                                                    > "$out"
    '');
 in mapAttrs go clustered
