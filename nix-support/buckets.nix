# Commands which split their input into various "buckets", e.g. based on
# clustering. We don't do any exploration or reduction, we just look at the
# resulting buckets.
{ bash, bc, format, jq, makeWrapper, stdenv, writeScript }:

rec {
  hashes = stdenv.mkDerivation {
    name        = "hashBuckets";
    buildInputs = [ bc jq makeWrapper ];
    src         = writeScript "hashBuckets-raw" ''
      #!${bash}/bin/bash
      set -e
      set -o pipefail

      INPUT=$(cat)

      # Wrap up raw objects into an array
      if echo "$INPUT" | jq -r 'type' | grep 'object' > /dev/null
      then
        INPUT=$(echo "$INPUT" | jq -s '.')
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

      export SIMPLE=1
      getHashes | "${format.fromStdin}"
    '';

    unpackPhase  = "true"; # Nothing to do
    doCheck      = true;
    checkPhase   = ''
      set -e
      echo "Testing empty input" 1>&2
      echo "" | "$src" 1 1 | jq -e 'length | . == 0'

      echo "Testing single input" 1>&2
      O='{"name":"foo", "type": "T", "quickspecable": true}'
      echo "[$O]" | "$src" 1 1 |
        jq -e --argjson o "$O" '. == [[$o + {"cluster":1}]]'
    '';
    installPhase = ''
      mkdir -p "$out/bin"
      makeWrapper "$src" "$out/bin/hashBucket" --prefix PATH : "${jq}/bin" \
                                               --prefix PATH : "${bc}/bin"
    '';
  };

  recurrent = abort "FIXME: Not implemented";
}
