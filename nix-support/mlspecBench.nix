{ annotated, bash, buckets, buildEnv, cluster, explore, fail, format,
  glibcLocales, hashspecBench, jq, lib, mkBin, nix-config, reduce-equations,
  runCommand, runWeka, stdenv, timeout, tipBenchmarks, writeScript }:
with builtins;
with lib;
with {
  inherit (nix-config) wrap;
};
rec {

  benchVars = {
    sampled = {
      inherit (hashspecBench.benchVars.sampled) genInput;

      runner  = wrap {
        name  = "mlspec-sampled-runner";
        paths = [ ((import hashspecBench.augmentedHs {
          hsDir = "${tipBenchmarks.tip-benchmark-haskell}";
        }).ghcWithPackages (h: map (n: h."${n}") [
          "quickspec" "murmur-hash" "cereal" "mlspec-helper"
          "tip-benchmark-sig" "runtime-arbitrary" "QuickCheck" "ifcxt"
          "hashable" "mlspec"
        ]))

        reduce-equations
        buckets.hashes
        runWeka ];
        script = inEnvScript;
      };
    };
  };

  ourEnv = writeScript "our-env.nix" ''
    with import ${./..}/nix-support {};
    buildEnv {
      name  = "mlspecbench-env";
      paths = [
        ((import ${hashspecBench.customHs}).ghcWithPackages (h: [
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

  inEnvScript = wrap {
    name   = "mlspecBench-inenvscript";
    paths  = [ bash explore.explore-theories jq reduce-equations timeout ];
    vars   = {
      NIX_EVAL_EXTRA_IMPORTS = ''[("tip-benchmark-sig", "A")]'';
      SIMPLE                 = "1";
    };
    script =  ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

      # Perform clustering
      CL=$(${cluster})

      clCount=$(echo "$CL" | jq 'map(.cluster) | max')
      ${assertNumeric "$clCount" "clCount should contain number of clusters"}

      export clCount

      if [[ -n "$EXPLORATION_MEM" ]]
      then
        echo "Limiting memory to '$EXPLORATION_MEM'" 1>&2
        export MAX_KB="$EXPLORATION_MEM"
      fi

      echo "$CL" | "${format.fromStdin}" |
        withTimeout explore-theories | reduce-equations
    '';
  };

  script = hashspecBench.wrapScript "mlspecBench" rawScript;

  mlGenInput = wrap {
    name   = "gen-input";
    paths  = [ bash jq tipBenchmarks.tools ];
    vars   = {
      OUT_DIR   = tipBenchmarks.tip-benchmark-haskell;
      ANNOTATED = annotated {
        pkgDir = toString tipBenchmarks.tip-benchmark-haskell;
      };
      filter = writeScript "filter.jq" ''
        def mkId: {"name": .name, "package": .package, "module": .module};

        def keep($id): $keepers | map(. == $id) | any;

        def setQS: . + {"quickspecable": (.quickspecable and keep(mkId))};

        map(setQS)
      '';
    };
    script = ''
      #!/usr/bin/env bash
      set -e
      set -o pipefail

      # Sample some names, give the default module and package, then slurp
      # into an array
      echo "Running 'choose_sample $1 $2'" 1>&2
      KEEPERS=$(choose_sample "$1" "$2" |
                jq -R '{"name"    : .,
                        "module"  : "A",
                        "package" : "tip-benchmark-sig"}' |
                jq -s '.')

      # Filters the signature to only those sampled in KEEPERS
      jq --argjson keepers "$KEEPERS" -f "$filter" < "$ANNOTATED" |
        jq 'map(select(.quickspecable))'
    '';
  };

  mlAllInput = wrap {
    name   = "all-input";
    paths  = [ fail ];
    script = ''
      #!/usr/bin/env bash
      set -e

      [[ -n "$ANNOTATED" ]] || fail "Got no ANNOTATED"

      ANN_F=$(readlink -f ANNOTATED)
      [[ -f "$ANN_F" ]] || fail "Annotated '$ANNOTATED' isn't a file (or link)"

      [[ -n "$OUT_DIR" ]] || fail "Got no OUT_DIR"

      OUT_D=$(readlink -f "$OUT_DIR")
      [[ -d "$OUT_D" ]] || fail "OUT_DIR '$OUT_DIR' isn't a dir (or link)"

      cat "$ANNOTATED"
    '';
  };

  rawScript = writeScript "mlspecBench" ''
    #!${bash}/bin/bash
    set -e

    ${hashspecBench.setUpDir}
    export TEMPDIR="$DIR"
    ${hashspecBench.getInput}

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
        INFO="$SAMPLE_SIZE" benchmark
      done
    else
      echo "No sample size given, using whole signature" 1>&2
      export GEN_INPUT="${mlAllInput}"
      INFO="" benchmark
    fi
  '';

  mls = mkBin {
    name = "mlspecBench";
    file = script;
  };
}
