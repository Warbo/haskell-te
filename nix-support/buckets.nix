# Commands which split their input into various "buckets", e.g. based on
# clustering. We don't do any exploration or reduction, we just look at the
# resulting buckets.
{ bash, bc, cluster, format, jq, mkBin, ghc, runCommand, runWeka, stdenv,
  withDeps, wrap, writeScript }:

with rec {
  hashes = mkBin {
    name   = "hashBucket";
    paths  = [ bash bc ghc jq ];
    vars   = { SIMPLE = "1"; };
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

      INPUT=$(cat)

      # Wrap up raw objects into an array
      if echo "$INPUT" | jq -r 'type' | grep 'object' > /dev/null
      then
        INPUT=$(echo "$INPUT" | jq -s '.')
      fi

      if [[ -n "$CLUSTER_SIZE" ]]
      then
        echo "Using cluster size of $CLUSTER_SIZE" 1>&2
        LENGTH=$(echo "$INPUT" | jq 'length')
        [[ -n "$LENGTH" ]] || LENGTH=0

        PROG=$(echo "main = print (ceiling (($LENGTH :: Float) / $CLUSTER_SIZE) :: Int)")
        CLUSTERS=$(echo "$PROG" | runhaskell)

        echo "Using $CLUSTERS clusters of length $CLUSTER_SIZE" 1>&2
      fi

      [[ -n "$CLUSTERS" ]] || {
        CLUSTERS=$(echo "$INPUT" | jq 'length | sqrt | . + 0.5 | floor')
        export CLUSTERS

        echo "No cluster count given; using $CLUSTERS (sqrt of sample size)" 1>&2
      }

      clCount="$CLUSTERS"
      export clCount

      function getHashes() {
        echo "Calculating SHA256 checksums of names" 1>&2
        while read -r ENTRY
        do
          NAME=$(echo "$ENTRY" | jq -r '.name')

          SHA=$(echo "clusters-$clCount-name-$NAME-entropy-input-$INPUT" |
                sha256sum | cut -d ' ' -f1 | tr '[:lower:]' '[:upper:]')

          # Convert hex to decimal. Use large BC_LINE_LENGTH to avoid line-
          # breaking.
          SHADEC=$(echo "ibase=16; $SHA" | BC_LINE_LENGTH=5000 bc)

          # Calculate modulo, now that both numbers are in decimal
          NUM=$(echo "$SHADEC % $CLUSTERS" | BC_LINE_LENGTH=5000 bc)

          # Cluster numbers start from 1
          echo "$ENTRY" | jq --argjson num "$NUM" '. + {"cluster": ($num + 1)}'
        done < <(echo "$INPUT" | jq -c '.[]') | jq -s '.'
      }

      getHashes | "${format.fromStdin}"
    '';
  };

  hashCheck = runCommand "hash-bucket-check" { buildInputs = [ hashes ]; } ''
    set -e
    set -o pipefail

    echo "Testing empty input" 1>&2
    echo "" | CLUSTER_SIZE=10 hashBucket 1 1 | jq -e 'length | . == 0'

    echo "Testing single input" 1>&2
    O='{"name":"foo", "type": "T", "quickspecable": true}'
    echo "[$O]" | CLUSTER_SIZE=10 hashBucket 1 1 |
      jq -e --argjson o "$O" '. == [[$o + {"cluster":1}]]'

    mkdir "$out"
  '';

  recurrent = mkBin {
    name   = "recurrentBucket";
    paths  = [ bash jq runWeka ];
    vars   = { SIMPLE = "1"; };
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

      # Perform clustering
      CLUSTERED=$(${cluster})

      clCount=$(echo "$CLUSTERED" | jq 'map(.cluster) | max')
      export clCount

      echo "$CLUSTERED" | "${format.fromStdin}"
    '';
  };
};

{
  inherit recurrent;
  hashes = withDeps [ hashCheck ] hashes;
}
