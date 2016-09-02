{ annotate, buildEnv, cluster, ensureVars, explore, glibcLocales,
  haskellPackages, jq, quickspecBench, reduce, writeScript }:
with builtins;

rec {
  doReduce = writeScript "doReduce.sh" ''
    ${reduce.preamble}

    getEqs | ${reduce.script}
  '';

  env = buildEnv {
    name  = "mlspecBench-env";
    paths = [ (haskellPackages.ghcWithPackages (h: [
                h.reduce-equations h.bench h.mlspec h.ML4HSFE
              ])) ];
  };

  inner = writeScript "mlspecBench-inner.sh" ''
    set -e
    set -o pipefail

    cat "$DIR/annotated.json"   |
    ${cluster.clusterScript}    |
    ${explore.explore-theories} |
    ${doReduce}
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
    }
    export TEMPDIR="$DIR"

    # Initialise all of the data we need
    SMT_FILE="$DIR/input.smt2"
    export SMT_FILE
    cat > "$SMT_FILE"

    ${quickspecBench.mkPkgInner}
    ${ensureVars ["OUT_DIR"]}

    STORED=$(nix-store --add "$OUT_DIR")
      EXPR="with import ${./..}/nix-support {}; annotated \"$STORED\""
         F=$(nix-build --show-trace -E "$EXPR")
    cp "$F" "$DIR/annotated.json"

    echo "${inner} < '$DIR/input.smt2'" > "$DIR/cmd.sh"
    chmod +x "$DIR/cmd.sh"

    # Run mlspec once to generate equations
    nix-shell -p ${env} --run "$DIR/cmd.sh" > "$DIR/eqs.json" || {
      echo "Failed to get eqs" 1>&2
      exit 1
    }

    # Run mlspec over and over to benchmark
    nix-shell -p ${env} --run \
      "bench --template json --output '$DIR/time.json' '$DIR/cmd.sh'" 1>&2 || {
      echo "Failed to benchmark" 1>&2
      exit 1
    }

    "${jq}/bin/jq" -n --slurpfile result "$DIR/eqs.json"  \
                      --slurpfile time   "$DIR/time.json" \
                   '{"time": $time, "result": $result}'
  '';
}
