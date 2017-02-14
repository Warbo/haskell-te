{ bash, buildEnv, cluster, ensureVars, explore, format, glibcLocales,
  haskellPackages, jq, lib, makeWrapper, nixEnv, quickspecBench,
  reduce-equations, runCommand, runWeka, stdenv, writeScript }:
with builtins;
with lib;

rec {

  inner = writeScript "mlspecBench-inner.sh" ''
    #!${bash}/bin/bash

  '';

  ourEnv = writeScript "our-env.nix" ''
    with import ${./..}/nix-support {};
    buildEnv {
      name  = "mlspecbench-env";
      paths = [
        ((import ${quickspecBench.customHs}).ghcWithPackages (h: [
          h.tip-benchmark-sig h.mlspec
        ]))
        runWeka
        jq
      ];
    }
  '';

  assertNumeric = var: msg:
    assert hasPrefix "$" var || abort (toString {
      function = "assertNumeric";
      error    = "Argument 'var' should be bash variable with '$'";
      inherit var msg;
    });
    ''
      echo "${var}" | grep -o "^[0-9][0-9]*\$" > /dev/null || {
        echo 'Error, ${var}' "(${var})" 'is not numeric: ${msg}' 1>&2
        exit 1
      }
    '';

  inEnvScript = writeScript "mlspecBench-inenvscript" ''
    #!${bash}/bin/bash
    set -e
    set -o pipefail

    function finish {
      rm "$DIR/clusters.json"
    }
    trap finish EXIT

    # Perform clustering
    clusters="$DIR/clusters.json"
    export clusters

    ${cluster.clusterScript} > "$clusters"

    clCount=$("${jq}/bin/jq" 'map(.cluster) | max' < "$DIR/clusters.json")
    ${assertNumeric "$clCount" "clCount should contain number of clusters"}

    export clusters
    export clCount

    NIX_EVAL_EXTRA_IMPORTS='[("tip-benchmark-sig", "A")]'
    export NIX_EVAL_EXTRA_IMPORTS

    export SIMPLE=1

    "${writeScript "format" format.script}" < "$DIR/clusters.json" |
      "${explore.explore-theories}"                                |
      "${reduce-equations}/bin/reduce-equations"
  '';

  script = runCommand "mlspecBench" { buildInputs = [ makeWrapper ]; } ''
    makeWrapper "${rawScript}" "$out"                                     \
      --prefix PATH :         "${quickspecBench.env}/bin"                 \
      --set    LANG           'en_US.UTF-8'                               \
      --set    LOCALE_ARCHIVE '${glibcLocales}/lib/locale/locale-archive' \
      --set    NIX_EVAL_HASKELL_PKGS "${quickspecBench.customHs}"         \
      --set    NIX_REMOTE     '${nixEnv.nixRemote}'                       \
      --set    NIX_PATH       'real=${toString <nixpkgs>}:nixpkgs=${toString ../nix-support}'
  '';

  mlGenInput = quickspecBench.mkGenInput (writeScript "gen-sig-ml" ''
    #!/usr/bin/env bash
    jq 'map(select(.quickspecable))'
  '');

  mlAllInput = writeScript "all-input" ''
    [[ -f "$ANNOTATED" ]] || {
      echo "Got no ANNOTATED" 1>&2
      exit 1
    }
    [[ -d "$OUT_DIR" ]] || {
      echo "Got no OUT_DIR" 1>&2
      exit 1
    }

    cat "$ANNOTATED"
  '';

  rawScript = writeScript "mlspecBench" ''
    #!${bash}/bin/bash
    set -e

    ${quickspecBench.setUpDir}
    export TEMPDIR="$DIR"
    ${quickspecBench.getInput}

    # Explore
    export    NIXENV="import ${ourEnv}"
    export       CMD="${inEnvScript}"

    if [[ -n "$SAMPLE_SIZES" ]]
    then
      echo "Looping through sample sizes" 1>&2
      for SAMPLE_SIZE in $SAMPLE_SIZES
      do
        echo "Limiting to a sample size of '$SAMPLE_SIZE'" 1>&2
        export GEN_INPUT="${mlGenInput}"
        INFO="$SAMPLE_SIZE" REPS=1 benchmark
      done
    else
      echo "No sample size given, using whole signature" 1>&2
      export GEN_INPUT="${mlAllInput}"
      INFO="" REPS=1 benchmark
    fi
  '';

  mls = stdenv.mkDerivation {
    name         = "mlspecBench";
    src          = script;
    buildInputs  = [ quickspecBench.env ];
    unpackPhase  = "true";  # Nothing to do

    doCheck      = true;
    checkPhase   = ''
      true
    '';
    installPhase = ''
      mkdir -p "$out/bin"
      cp "$src" "$out/bin/mlspecBench"
    '';
  };
}
