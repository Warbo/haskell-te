{ bash, bc, explore, format, glibcLocales, makeWrapper, mlspecBench, nixEnv,
  quickspecBench, reduce-equations, runCommand, stdenv, timeout, writeScript }:

rec {

  inEnvScript = writeScript "mlspecBench-inenvscript" ''
    #!${bash}/bin/bash
    set -e
    set -o pipefail

    # Perform clustering
    clusters="$DIR/clusters.json"
    export clusters

    INPUT=$(cat)
    [[ -n "$CLUSTERS" ]] || {
      CLUSTERS=$(echo "$INPUT" | jq -s '. | length | sqrt | . + 0.5 | floor')
      export CLUSTERS

      echo "No cluster count given; using $CLUSTERS (sqrt of sample size)" 1>&2
    }
    ${mlspecBench.assertNumeric "$CLUSTERS"
                                "CLUSTERS should contain number of clusters"}
    clCount="$CLUSTERS"
    export clCount

    echo "Calculating SHA256 checksums of names" 1>&2
    while read -r ENTRY
    do
      SHA=$(echo "$ENTRY" | jq -r '.name' | sha256sum | cut -d ' ' -f1 |
            tr '[:lower:]' '[:upper:]')

      # Convert hex to decimal. Use large BC_LINE_LENGTH to avoid line-breaking.
      SHADEC=$(echo "ibase=16; $SHA" | BC_LINE_LENGTH=5000 bc)

      # Calculate modulo, now that both numbers are in decimal
      NUM=$(echo "$SHADEC % $CLUSTERS" | BC_LINE_LENGTH=5000 bc)

      # Cluster numbers start from 1
      echo "$ENTRY" | jq --argjson num "$NUM" '. + {"cluster": ($num + 1)}'
    done < <(echo "$INPUT" | jq -c '.[]') | jq -s '.' > "$clusters"

    NIX_EVAL_EXTRA_IMPORTS='[("tip-benchmark-sig", "A")]'
    export NIX_EVAL_EXTRA_IMPORTS

    export SIMPLE=1

    if [[ -n "$EXPLORATION_MEM" ]]
    then
      echo "Limiting memory to '$EXPLORATION_MEM'" 1>&2
      export MAX_KB="$EXPLORATION_MEM"
    fi

    echo "Exploring" 1>&2
    "${writeScript "format" format.script}" < "$clusters"        |
      "${timeout}/bin/withTimeout" "${explore.explore-theories}" |
      "${reduce-equations}/bin/reduce-equations"
  '';

  script = runCommand "hashspecBench" { buildInputs = [ makeWrapper ]; } ''
    makeWrapper "${rawScript}" "$out"                                     \
      --prefix PATH :         "${quickspecBench.env}/bin"                 \
      --prefix PATH :         "${bc}/bin"                                 \
      --set    LANG           'en_US.UTF-8'                               \
      --set    LOCALE_ARCHIVE '${glibcLocales}/lib/locale/locale-archive' \
      --set    NIX_EVAL_HASKELL_PKGS "${quickspecBench.customHs}"         \
      --set    NIX_REMOTE     '${nixEnv.nixRemote}'                       \
      --set    NIX_PATH       'real=${toString <nixpkgs>}:nixpkgs=${toString ../nix-support}'
  '';

  rawScript = writeScript "hashspecBench" ''
    #!${bash}/bin/bash
    set -e

    ${quickspecBench.setUpDir}
    export TEMPDIR="$DIR"
    ${quickspecBench.getInput}

    # Explore
    export    NIXENV="import ${mlspecBench.ourEnv}"
    export       CMD="${inEnvScript}"

    if [[ -n "$SAMPLE_SIZES" ]]
    then
      echo "Looping through sample sizes" 1>&2
      for SAMPLE_SIZE in $SAMPLE_SIZES
      do
        echo "Limiting to a sample size of '$SAMPLE_SIZE'" 1>&2
        export GEN_INPUT="${mlspecBench.mlGenInput}"
        INFO="$SAMPLE_SIZE" benchmark
      done
    else
      echo "No sample size given, using whole signature" 1>&2
      export GEN_INPUT="${mlspecBench.mlAllInput}"
      INFO="" benchmark
    fi
  '';

  hs = stdenv.mkDerivation {
    name         = "hashspecBench";
    src          = script;
    buildInputs  = [ quickspecBench.env ];
    unpackPhase  = "true";  # Nothing to do

    doCheck      = true;
    checkPhase   = ''
      true
    '';

    installPhase = ''
      mkdir -p "$out/bin"
      cp "$src" "$out/bin/hashspecBench"
    '';
  };
}
