{ bash, bc, explore, format, glibcLocales, makeWrapper, mlspecBench, nixEnv,
  quickspecBench, reduce-equations, runCommand, stdenv, timeout, writeScript }:

rec {

  inEnvScript = runCommand "hashspecBench-inenvscript"
    {
      raw = writeScript "hashspecBench-inenvscript-raw" ''
        #!/usr/bin/env bash

        NIX_EVAL_EXTRA_IMPORTS='[("tip-benchmark-sig", "A")]'
        export NIX_EVAL_EXTRA_IMPORTS

        if [[ -n "$EXPLORATION_MEM" ]]
        then
          echo "Limiting memory to '$EXPLORATION_MEM'" 1>&2
          export MAX_KB="$EXPLORATION_MEM"
        fi

        echo "Exploring" 1>&2
        hashBucket | withTimeout "${explore.explore-theories}" | reduce-equations
      '';
      buildInputs = [ makeWrapper ];
    }
    ''
      makeWrapper "$raw" "$out" --prefix PATH : "${reduce-equations}/bin" \
                                --prefix PATH : "${timeout}/bin"          \
                                --prefix PATH : "${buckets.hashes}/bin"
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
