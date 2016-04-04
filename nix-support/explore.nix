{ benchmark, explore-theories, lib, ml4hs, parseJSON, runScript, withNix,
  writeScript }:
with lib;

{ quick, clustered }:

let formatAndExplore = writeScript "format-and-explore" ''
      set -e
      "${ml4hs}/lib/ml4hs/format-exploration.sh" | explore-theories
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
