{ annotated, bash, buckets, explore, fail, format, glibcLocales, jq,
  mlspecBench, nix-config, quickspecBench, reduce-equations, runCommand,
  stdenv, timeout, tipBenchmarks, wrap, writeScript }:

with builtins;
rec {

  benchVars = {
    sampled = {
      runner  = wrap {
        name  = "hashspec-sampled-runner";
        paths = [ ((import quickspecBench.augmentedHs {
                     hsDir = "${tipBenchmarks.tip-benchmark-haskell}";
                   }).ghcWithPackages (h: map (n: h."${n}") [
                     "quickspec" "murmur-hash" "cereal" "mlspec-helper"
                     "tip-benchmark-sig" "runtime-arbitrary" "QuickCheck" "ifcxt"
                     "hashable" "mlspec"
                   ]))

                   reduce-equations
                   buckets.hashes
                   fail
                   explore.explore-theories
                 ];
        vars   = {
          NIX_EVAL_EXTRA_IMPORTS = ''[("tip-benchmark-sig", "A")]'';
        };
        script = ''
          #!/usr/bin/env bash
          set -e
          [[ -n "$TEMPDIR" ]] || fail "No TEMPDIR given"

          [[ -n "$MAX_KB"  ]] || {
            echo "Setting default memory limit of 2GB" 1>&2
            export MAX_KB=2000000
          }

          hashBucket | explore-theories | reduce-equations
        '';
      };

      genInput = wrap {
        name  = "hashspec-sampled-gen-input";
        paths = [ fail jq tipBenchmarks.tools ];
        vars  = {
          OUT_DIR   = tipBenchmarks.tip-benchmark-haskell;

          ANNOTATED = annotated (toString tipBenchmarks.tip-benchmark-haskell);

          FILTER = writeScript "filter.jq" ''
            def mkId: {"name": .name, "package": .package, "module": .module};

            def keep($id): $keepers | map(. == $id) | any;

            def setQS: . + {"quickspecable": (.quickspecable and keep(mkId))};

            map(setQS)
          '';
        };
        script = ''
          #!/usr/bin/env bash
          set -e

          [[ -n "$ANNOTATED" ]] || fail "No ANNOTATED given"
          [[ -n "$OUT_DIR"   ]] || fail "No OUT_DIR given"

          # Give sampled names a module and package, then slurp into an array
          KEEPERS=$(jq -R '{"name"    : .,
                            "module"  : "A",
                            "package" : "tip-benchmark-sig"}' |
                    jq -s '.')

          # Filters the signature to only those sampled in KEEPERS
          jq --argjson keepers "$KEEPERS" -f "$FILTER" < "$ANNOTATED" |
            jq 'map(select(.quickspecable))'
        '';
      };
    };
  };

  inEnvScript = wrap {
    name   = "hashspecBench-inenvscript";
    paths  = [
      bash explore.explore-theories reduce-equations timeout buckets.hashes
    ];
    vars   = {
      NIX_EVAL_EXTRA_IMPORTS = ''[("tip-benchmark-sig", "A")]'';
    };
    script = ''
      #!/usr/bin/env bash

      if [[ -n "$EXPLORATION_MEM" ]]
      then
        echo "Limiting memory to '$EXPLORATION_MEM'" 1>&2
        export MAX_KB="$EXPLORATION_MEM"
      fi

      echo "Exploring" 1>&2
      hashBucket | withTimeout explore-theories | reduce-equations
    '';
    };

  script = quickspecBench.wrapScript "hashspecBench" rawScript;

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
