{ annotated, bash, buckets, buildEnv, concurrentQuickspec, fail,
  glibcLocales, jq, mlspecBench, nix, nixEnv, reduce-equations, runCommand,
  stdenv, testData, timeout, tipBenchmarks, wrap, writeScript }:

with builtins;
rec {
  benchVars = {
    sampled = {
      runner  = wrap {
        name  = "hashspec-sampled-runner";
        paths = [ ((import ../nix-support/augmentedHs.nix {
                     hsDir = "${tipBenchmarks.tip-benchmark-haskell}";
                   }).ghcWithPackages (h: map (n: h."${n}") [
                     "quickspec" "murmur-hash" "cereal" "mlspec-helper"
                     "tip-benchmark-sig" "runtime-arbitrary" "QuickCheck" "ifcxt"
                     "hashable" "mlspec"
                   ]))

                   reduce-equations
                   buckets.hashes
                   fail
                   concurrentQuickspec
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

          hashBucket | concurrentQuickspec | reduce-equations
        '';
      };

      genInput = wrap {
        name  = "hashspec-sampled-gen-input";
        paths = [ fail jq tipBenchmarks.tools ];
        vars  = {
          OUT_DIRS  = toJSON [tipBenchmarks.tip-benchmark-haskell];

          ANNOTATED = annotated {
            pkgDir = toString tipBenchmarks.tip-benchmark-haskell;
          };

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
          set -o pipefail

          [[ -n "$ANNOTATED" ]] || fail "No ANNOTATED given"
          [[ -n "$OUT_DIRS"  ]] || fail "No OUT_DIRS given"

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

  setUpDir = ''
    [[ -n "$DIR" ]] || {
      echo "No DIR given to work in, using current directory $PWD" 1>&2
      DIR="$PWD"
    }
    export DIR
  '';

  mkPkgInner = wrap {
    name  = "mkPkgInner";
    paths = [ fail ];
    vars  = {
      MAKE_PACKAGE = wrap {
        name   = "make-haskell-package";
        paths  = [ tipBenchmarks.tools ];
        script = ''
          OUT_DIRS="[\"$PWD\"]" full_haskell_package < "$INPUT_TIP"
        '';
      };
    };
    script = ''
      #!/usr/bin/env bash
      set -e
      [[ -n "$INPUT_TIP" ]] || fail "No INPUT_TIP given, aborting"

      echo "Creating Haskell package" 1>&2
      mkdir "generated-haskell-package"
      pushd "generated-haskell-package" > /dev/null
        "$MAKE_PACKAGE" || fail "Failed to create Haskell package"
      popd > /dev/null
      echo "Created Haskell package" 1>&2
    '';
  };

  env = buildEnv {
    name  = "te-env";
    paths = [ jq nix tipBenchmarks.tools ];
  };

  hs-untested = mkBin {
    name  = "hashspecBench";
    paths = [ bash env haskellPkgToAsts jq ];
    vars  = {
      CMD      = wrap {
        name   = "hashspecBench-inenvscript";
        paths  = [
          bash concurrentQuickspec reduce-equations timeout buckets.hashes
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
          hashBucket | withTimeout concurrentQuickspec | reduce-equations
        '';
      };
      NIXENV   = "import ${mlspecBench.ourEnv}";
      SKIP_NIX = "1";
      LANG                  = "en_US.UTF-8";
      LOCALE_ARCHIVE        = "${glibcLocales}/lib/locale/locale-archive";
      NIX_EVAL_HASKELL_PKGS = ../nix-support/customHs.nix;
      NIX_PATH              = concatStringsSep ":" [
        "nixpkgs=${toString <nixpkgs>}"
        "support=${toString ./..}"
      ];
    };
    script = ''
      #!/usr/bin/env bash
      set -e

      ${setUpDir}
      export TEMPDIR="$DIR"
      pushd "$DIR" > /dev/null
        INPUT_TIP="$PWD/input_tip"
        cat > "$INPUT_TIP"
        OUT_DIR=$("$mkPkgInner")
        export OUT_DIR
        ANNOTATED=$(haskellPkgToAsts "$OUT_DIR")
        export ANNOTATED
      popd > /dev/null

      # FIXME: OUT_DIR/OUT_DIRS confusion here

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
  };

  MAX_SECS = "300";
  testFile = name: path: runCommand "hs-${name}"
    {
      inherit MAX_SECS;
      buildInputs = [ fail jq hs-untested ];
    }
    ''
      set -e
      echo "Running ${name} through hashspecBench" 1>&2
      OUTPUT=$(hashspecBench < "${path}") ||
        fail "Couldn't explore ${name}"

      T=$(echo "$OUTPUT" |
          jq 'has("cmd") and has("info") and has("results")') ||
        fail "Couldn't parse output\nSTART\n$OUTPUT\nEND"

      [[ "x$T" = "xtrue" ]] ||
        fail "Required fields missing:\n$OUTPUT"

      mkdir "$out"
    '';

  hs = withDeps
    [
      (testFile "list-full"  ../benchmarks/list-full.smt2)
      (testFile "nat-full"   ../benchmarks/nat-full.smt2)
      (testFile "nat-simple" ../benchmarks/nat-simple.smt2)
      (attrValues (mapAttrs
        (name: runCommand name {
                 inherit MAX_SECS;
                 buildInputs = [ fail hs-untested tipBenchmarks.tools ];
               })
        {
          canRun = ''
            set -e
            hashspecBench < "${testData.tip.test-theory}"
            mkdir "$out"
          '';

          outputIsJson = ''
            set -e
            OUTPUT=$(hashspecBench < ${testData.tip.test-theory})

            TYPE=$(echo "$OUTPUT" | jq -r 'type') ||
              fail "START OUTPUT\n$OUTPUT\nEND OUTPUT"

            [[ "x$TYPE" = "xobject" ]] ||
              fail "START OUTPUT\n$OUTPUT\nEND OUTPUT\nGot '$TYPE' not object"

            mkdir "$out"
          '';

          haveEquations = ''
            set -e
            OUTPUT=$(hashspecBench < ${testData.tip.test-theory}) || exit 1
             CHECK=$(echo "$OUTPUT" | jq 'has("results")')        || exit 1
            [[ "x$CHECK" = "xtrue" ]] ||
              fail "Didn't find 'results' in\n$OUTPUT"
            mkdir "$out"
          '';

          filterSamples =
            with {
              keepers = map (name: {
                              inherit name;
                              module  = "A";
                              package = "tip-benchmark-sig";
                            }) [ "append" "constructorNil" "constructorCons" ];
            };
            ''
              set -e

              BENCH_OUT=$(CLUSTERS=1 SAMPLE_SIZES="5" hashspecBench)

              # Get all the constant symbols in all equations
              STDOUTS=$(echo "$BENCH_OUT" | jq -r '.results | .[] | .stdout') ||
                fail "Couldn't get stdouts\n\n$BENCH_OUT"

              OUTPUTS=$(while read -r F
                        do
                          cat "$F"
                        done < <(echo "$STDOUTS")) ||
                fail "Couldn't concat stdouts\n\n$BENCH_OUT\n\n$STDOUTS"

              EQS=$(echo "$OUTPUTS" | grep -v '^Depth') ||
                fail "Couldn't get eqs\n\n$BENCH_OUT\n\n$OUTPUTS"

              NAMES=$(echo "$EQS" |
                jq -r 'getpath(paths(type == "object" and .role == "constant"))
                       | .symbol' | sort -u) ||
                fail "Couldn't get names\n\n$BENCH_OUT\n\n$EQS"
              SAMPLE=$(choose_sample 5 1)

              # Remove any names which appear in the sample
              while read -r NAME
              do
                NAMES=$(echo "$NAMES" | grep -vFx "$NAME") || true
              done < <(echo "$SAMPLE")

              # If there are any names remaining, they weren't in the sample
              if echo "$NAMES" | grep '^.' > /dev/null
              then
                DBG="NAMES:\n$NAMES\n\nOUTPUT:\n$BENCH_OUT\nSAMPLE:\n$SAMPLE"
                fail "Found names which aren't in sample\n$DBG"
              fi

              mkdir "$out"
            '';
        }))
    ]
    hs-untested;
}
