{ cluster, ensureVars, explore, format, glibcLocales, jq, quickspecBench,
  reduce-equations, runWeka, writeScript }:
with builtins;

rec {

  doExplore = writeScript "doExplore.sh" ''
    #!/usr/bin/env bash

    export SIMPLE=1
    "${writeScript "format" format.script}" | "${explore.explore-theories}"
  '';

  inner = writeScript "mlspecBench-inner.sh" ''
    set -e
    set -o pipefail

    clusters="$DIR/clusters.json"
    ${cluster.clusterScript} > "$clusters"

    clCount=$("${jq}/bin/jq" 'map(.cluster) | max' < "$clusters")

    NIX_EVAL_EXTRA_IMPORTS='[("tip-benchmark-sig", "A")]'

    export clusters
    export clCount
    export NIX_EVAL_EXTRA_IMPORTS

    ${doExplore} | tee >(cat >&2) | "${reduce-equations}/bin/reduce-equations"
  '';

  ourEnv = writeScript "our-env.nix" ''
    with import ${./..}/nix-support {};
    buildEnv {
      name  = "mlspecbench-env";
      paths = [
        ((import ${quickspecBench.customHs}).ghcWithPackages (h: [
          h.tip-benchmark-sig h.bench h.mlspec h.ML4HSFE
        ]))
        runWeka
        jq
      ];
    }
  '';

  script = writeScript "mlspecBench" ''
    set -e

    # Required for Unicode in Haskell and Perl
    export LANG='en_US.UTF-8'
    export LOCALE_ARCHIVE='${glibcLocales}/lib/locale/locale-archive'

    # Make a temp dir if we've not got one, and remove it on exit
    [[ -z "$OUR_DIR" ]] || {
      echo "OUR_DIR must be empty, since we delete it on exit" 1>&2
      exit 1
    }

    function cleanup {
      if [[ -n "$OUR_DIR" ]] && [[ -d "$OUR_DIR" ]]
      then
        rm -rf "$OUR_DIR"
      fi
    }
    trap cleanup EXIT

    [[ -n "$DIR" ]] || {
      OUR_DIR=$(mktemp -d --tmpdir "mlspecBenchXXXXX")
      DIR="$OUR_DIR"
      echo "Creating temp dir '$OUR_DIR'" 1>&2
    }
    export TEMPDIR="$DIR"

    # Initialise all of the data we need
    ${quickspecBench.mkPkgInner}
    ${ensureVars ["OUT_DIR"]}

    EXPR="with import ${./..}/nix-support {}; annotated \"$OUT_DIR\""

    echo "Annotating, via '$EXPR'" 1>&2
    F=$(nix-build --show-trace -E "$EXPR")

    "${quickspecBench.filterSample}" < "$F" > "$DIR/filtered.json"

    echo "DIR='$DIR' ${inner} < '$DIR/filtered.json'" > "$DIR/cmd.sh"
    chmod +x "$DIR/cmd.sh"

    # Make sure our generated package is available to Nix
    NIX_EVAL_HASKELL_PKGS="${quickspecBench.customHs}"
    export NIX_EVAL_HASKELL_PKGS

    # Run mlspec once to generate equations
    nix-shell --show-trace -p '(import ${ourEnv})' \
              --run "$DIR/cmd.sh" > "$DIR/eqs.json" || {
      echo "Failed to get eqs" 1>&2
      exit 1
    }

    # Run mlspec over and over to benchmark
    if [[ "$DO_BENCH" -eq 1 ]]
    then
      nix-shell --show-trace -p '(import ${ourEnv})' --run \
        "bench --template json --output '$DIR/time.json' '$DIR/cmd.sh'" 1>&2 || {
        echo "Failed to benchmark" 1>&2
        exit 1
      }
    else
      echo "Not benchmarking. To benchmark, set DO_BENCH env var to 1" 1>&2
      echo '"Not benchmarked"' > "$DIR/time.json"
    fi

    "${jq}/bin/jq" -n --slurpfile time   "$DIR/time.json" \
                      --slurpfile result "$DIR/eqs.json"  \
                      '{"time": $time, "result": $result}'
  '';
}
