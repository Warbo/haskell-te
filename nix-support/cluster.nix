{ benchmark, parseJSON, recurrent-clustering, runScript, writeScript }:
with builtins;

let

wekaCli = toString ../packages/runWeka/weka-cli.nix;

nixRecurrentClusteringScript = writeScript "nix-recurrent-clustering" ''
  set -e

  [[ -e "${wekaCli}" ]] || {
    echo "Cannot find '${wekaCli}'" 1>&2
    exit 1
  }

  if command -v weka-cli > /dev/null
  then
    "${toString ../recurrent-clustering/recurrentClustering}"
  else
    echo "No weka-cli found" 1>&2
    exit 2
  fi
'';

clusterScript = writeScript "cluster" ''
  set -e
  export RUN_WEKA_CMD="${toString ../packages/runWeka/runWeka}"
  export WIDTH=30
  export HEIGHT=30
  ml4hsfe-loop | "${nixRecurrentClusteringScript}"
'';

cluster = { quick, annotated, clusters }: let

  go = c: parseJSON
            (runScript { buildInputs = [ recurrent-clustering ]; } ''
              set -e
              export CLUSTERS="${toString c}"
              "${benchmark quick "${clusterScript}" []}" < "${annotated}" > "$out"
            '');

  results = listToAttrs (map (c: { name  = toString c;
                                   value = go c; })
                        clusters);

  result = { inherit results;
             failed = any (n: results.${n}.failed) (attrNames results); };

  checkedResult = assert isAttrs results;
                  assert all (n: isInt (fromJSON n))    (attrNames results);
                  assert all (n: results.${n} ? stdout) (attrNames results);
                  assert all (n: results.${n} ? time)   (attrNames results);
                  result;

  in if result.failed then result
                      else checkedResult;

in { inherit cluster nixRecurrentClusteringScript; }
