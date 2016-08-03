{ benchmark, explore, jq, ML4HSFE, parseJSON, runScript, runWeka, writeScript }:
with builtins;

let

recurrentClusteringScript = writeScript "recurrent-clustering" ''
  #!/usr/bin/env bash
  set -e

  function msg {
    echo -e "$1" 1>&2
  }

  # shellcheck disable=SC2153
  [[ -n "$CLUSTERS" ]] || {
    msg "No CLUSTERS found in environment"
    exit 1
  }

  BASE=$(dirname "$0")
  DEPS=$(cat)

  while read -r SCC
  do
    msg "Next SCC"
    DEPS=$(echo "$DEPS" | jq --slurpfile scc <(echo "$SCC") \
             'map(. as $elem | if ($scc[0] | map(.name == $elem.name and .module == $elem.module and .package == $elem.package) | any) then . + {"tocluster":true} else . end)')

    # Update all features with the latest clusters

    # Look up an ID in $deps
    # shellcheck disable=SC2016
    COND2='.name == $this.name and .module == $this.module and .package == $this.package'

    # shellcheck disable=SC2016
    LOOKUP='(. as $this | $deps | map(select('"$COND2"') | .cluster) | . + [0] | .[0] | . + 300)'
    FEATURES="(.features | map(if type == \"object\" then ($LOOKUP) else . end))"

    # Cluster. We call runWeka directly since nix-shell adds a lot of
    # overhead, which we move outside the loop to our own invocation
    msg "Clustering..."
    # shellcheck disable=SC2016
    CLUSTERED=$(
      echo "$DEPS" |
      jq '. as $deps | $deps | map(. + {"features": '"$FEATURES"'})' |
      runWeka)

    # Add new clusters to DEPS
    msg "Collating..."
    # shellcheck disable=SC2016
    DEPS=$(echo "$DEPS" | jq --argfile clustered <(echo "$CLUSTERED") \
                             'map(. as $this | $clustered | map(select(.name == $this.name and .module == $this.module and .package == $this.package)) | map(.cluster) | if length == 1 then $this + {"cluster": .[0]} else $this end)')
  done < <(echo "$DEPS" | order-deps | jq -c '.[]')

  msg "Done"
  echo "$DEPS"
'';

nixRecurrentClusteringScript = writeScript "nix-recurrent-clustering" ''
  set -e

  if command -v weka-cli > /dev/null
  then
    "${recurrentClusteringScript}"
  else
    echo "No weka-cli found" 1>&2
    exit 2
  fi
'';

clusterScript = writeScript "cluster" ''
  set -e
  export WIDTH=30
  export HEIGHT=30
  ml4hsfe-outer-loop
'';

cluster = { quick, annotated, clusters }: let

  go = c: parseJSON
            (runScript { buildInputs = [ jq runWeka ML4HSFE ] ++
                                       (explore.extractedEnv null annotated); } ''
              set -e
              export CLUSTERS="${toString c}"
              "${benchmark {
                   inherit quick;
                   cmd    = clusterScript;
                   inputs = [annotated];
               }}" < "${annotated}" > "$out"
            '');

  results = listToAttrs (map (c: { name  = toString c;
                                   value = go c; })
                        clusters);

  result = { inherit results;
             failed = any (n: results."${n}".failed) (attrNames results); };

  checkedResult = assert isAttrs results;
                  assert all (n: isInt (fromJSON n))    (attrNames results);
                  assert all (n: results."${n}" ? stdout) (attrNames results);
                  assert all (n: results."${n}" ? time)   (attrNames results);
                  result;

  in if result.failed then result
                      else checkedResult;

in { inherit cluster nixRecurrentClusteringScript recurrentClusteringScript; }
