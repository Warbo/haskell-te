{ annotated, bash, buckets, buildEnv, explore, fail, format, glibcLocales, jq,
  mlspecBench, nix, nix-config, nixEnv, reduce-equations, runCommand, stdenv,
  timeout, tipBenchmarks, wrap, writeScript }:

with builtins;
rec {
  benchVars = {
    sampled = {
      runner  = wrap {
        name  = "hashspec-sampled-runner";
        paths = [ ((import augmentedHs {
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

  # We use "./.." so that all of our dependencies get included
  augmentedHs = writeScript "augmented-hs.nix" ''
    # Provides a set of Haskell packages for use by nix-eval.
    { hsDir }:
    with import ${./..}/nix-support {};
    with builtins;
    let hsName = "tip-benchmark-sig";  # The name used by full_haskell_package
        hsPkgs = haskellPackages.override {
          overrides = self: super:
            # Include existing overrides, along with our new one
            hsOverride self super // {
              "tip-benchmark-sig" = self.callPackage (toString (nixedHsPkg hsDir)) {};
            };
        };
        # Echo "true", with our Haskell package as a dependency
        check = stdenv.mkDerivation {
          name = "check-for-pkg";
          buildInputs  = [(hsPkgs.ghcWithPackages (h: [h."tip-benchmark-sig"]))];
          buildCommand = "source $stdenv/setup; echo true > $out";
        };
     in assert hsDir  != ""                 || abort "Got no OUT_DIR";
        assert hsPkgs ? "tip-benchmark-sig" || abort "hsPkgs doesn't have pkg";
        assert import "''${check}"          || abort "Couldn't build pkg";
        hsPkgs
  '';

  customHs = writeScript "custom-hs.nix" ''
    # Uses OUT_DIR env var to include the package generated from smtlib data
    (import <nixpkgs> {}).callPackage "${augmentedHs}" {
      hsDir = builtins.getEnv "OUT_DIR";
    }
  '';

  wrapScript = name: script: wrap {
    inherit name script;
    paths = [ env ];
    vars  = nixEnv // {
      LANG                  = "en_US.UTF-8";
      LOCALE_ARCHIVE        = "${glibcLocales}/lib/locale/locale-archive";
      NIX_EVAL_HASKELL_PKGS = customHs;
      NIX_PATH              = concatStringsSep ":" [
        "nixpkgs=${toString <nixpkgs>}"
        "support=${toString ../nix-support}"
      ];
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

    setUpDir = ''
      [[ -n "$DIR" ]] || {
        echo "No DIR given to work in, using current directory $PWD" 1>&2
        DIR="$PWD"
      }
      export DIR
    '';

    mkPkgInner = wrap {
      name  = "mkPkgInner";
      paths = [ fail inNixedDir ];
      vars  = {
        MAKE_PACKAGE = wrap {
          name   = "make-haskell-package";
          paths  = [ tipBenchmarks.tools ];
          script = ''
            OUT_DIR="$PWD" full_haskell_package < "$INPUT_TIP"
          '';
        };
      };
      script = ''
        #!/usr/bin/env bash
        set -e
        [[ -n "$INPUT_TIP" ]] || fail "No INPUT_TIP given, aborting"

        echo "Creating Haskell package" 1>&2
        inNixedDir "$MAKE_PACKAGE" "generated-haskell-package" ||
          fail "Failed to create Haskell package"
        echo "Created Haskell package" 1>&2
      '';
    };

    getInput = ''
      INPUT_TIP=$(pipeToNix)
      export INPUT_TIP

      echo "Input stored at '$INPUT_TIP'" 1>&2

      # Initialise all of the data we need
      OUT_DIR=$("$mkPkgInner")

      export OUT_DIR

      # Extract ASTs from the Haskell package, annotate and add to the Nix
      # store. By doing this in nix-build, we get content-based caching for free
      STORED=$(nix-store --add "$OUT_DIR")
      EXPR="with import <support> {}; annotated { pkgDir = \"$STORED\"; }"
      ANNOTATED=$(nix-build --show-trace -E "$EXPR")

      export ANNOTATED
    '';

  env = buildEnv {
    name  = "te-env";
    paths = [ jq nix tipBenchmarks.tools ];
  };

  script = wrapScript "hashspecBench" rawScript;

  rawScript = writeScript "hashspecBench" ''
    #!${bash}/bin/bash
    set -e

    ${setUpDir}
    export TEMPDIR="$DIR"
    ${getInput}

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

  hs-untested = stdenv.mkDerivation {
    name         = "hashspecBench";
    src          = script;
    buildInputs  = [ env ];
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

  maxSecs  = "300";
  testFile = name: path: runCommand "hs-${name}"
    {
      buildInputs = [ fail jq package ];
      MAX_SECS    = maxSecs;
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
                 buildInputs = [ fail package tipBenchmarks.tools ];
                 MAX_SECS    = maxSecs;
               })
        {
          canRun = ''
            set -e
            hashspecBench < "${./example.smt2}"
            mkdir "$out"
          '';

          outputIsJson = ''
            set -e
            OUTPUT=$(hashspecBench < ${./example.smt2})

            TYPE=$(echo "$OUTPUT" | jq -r 'type') ||
              fail "START OUTPUT\n$OUTPUT\nEND OUTPUT"

            [[ "x$TYPE" = "xobject" ]] ||
              fail "START OUTPUT\n$OUTPUT\nEND OUTPUT\nGot '$TYPE' not object"

            mkdir "$out"
          '';

          haveEquations = ''
            set -e
            OUTPUT=$(hashspecBench < ${./example.smt2})    || exit 1
             CHECK=$(echo "$OUTPUT" | jq 'has("results")') || exit 1
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
