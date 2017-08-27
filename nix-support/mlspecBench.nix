{ bash, buckets, buildEnv, cluster, ensureVars, explore, format, glibcLocales,
  hashspecBench, haskellPackages, jq, lib, nix-config,
  quickspecBench, reduce-equations, runCommand, runWeka, stdenv, timeout,
  tipBenchmarks, writeScript }:
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
        paths = [ ((import quickspecBench.augmentedHs {
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
      CL=$(${cluster.clusterScript})

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

  script = quickspecBench.wrapScript "mlspecBench" rawScript;

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
        INFO="$SAMPLE_SIZE" benchmark
      done
    else
      echo "No sample size given, using whole signature" 1>&2
      export GEN_INPUT="${mlAllInput}"
      INFO="" benchmark
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
