{ annotated, bash, benchmark, buildEnv, ensureVars, glibcLocales,
  haskellPackages, jq, lib, makeWrapper, nix, nix-config, nixEnv, runCmd,
  runCommand, stdenv, time, timeout, tipBenchmarks, withNix, writeScript }:

# Provides a script which accepts smtlib data, runs it through QuickSpec and
# outputs the resulting equations

with builtins; with lib;

rec {

inherit (nix-config) wrap;

fail = msg: ''{ echo -e "${msg}" 1>&2; exit 1; }'';

qsGenerateSig =
  with rec {
    runGenCmd = wrap {
      name  = "quickspec-run-gen-cmd";
      file  = getCmd;
      paths = [ (haskellPackages.ghcWithPackages (h: [ h.mlspec h.nix-eval ])) ];
      vars  = {
        #NIX_PATH = innerNixPath;
        NIX_EVAL_HASKELL_PKGS = customHs;
      };
    };
  };
  wrap {
    name   = "quickspec-generate-sig";
    paths  = [ jq ];
    script = ''
      #!/usr/bin/env bash
      jq 'map(select(.quickspecable))' | "${runGenCmd}"
    '';
  };

benchVars = {
  sampled = {
    runner  = wrap {
      name  = "quickspec-sampled-runner";
      paths = [ ((import augmentedHs {
                   hsDir = "${tipBenchmarks.tip-benchmark-haskell}";
                 }).ghcWithPackages (h: map (n: h."${n}") [
                   "quickspec" "murmur-hash" "cereal" "mlspec-helper"
                   "tip-benchmark-sig" "runtime-arbitrary" "QuickCheck" "ifcxt"
                   "hashable"
                 ])) ];
      script = ''
        #!/usr/bin/env bash
        cat | $*
      '';
    };

    genInput = wrap {
      name  = "quickspec-sampled-gen-input";
      paths = [ jq tipBenchmarks.tools ];
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

        [[ -n "$ANNOTATED" ]] || ${fail "No ANNOTATED given"}
        [[ -n "$OUT_DIR"   ]] || ${fail "No OUT_DIR given"}

        # Give sampled names a module and package, then slurp into an array
        KEEPERS=$(jq -R '{"name"    : .,
                          "module"  : "A",
                          "package" : "tip-benchmark-sig"}' |
                  jq -s '.')

        # Filters the signature to only those sampled in KEEPERS
        jq --argjson keepers "$KEEPERS" -f "$FILTER" < "$ANNOTATED" |
          "${qsGenerateSig}"
        '';
      };
  };

  # For exploring an arbitrary theory supplied via stdin
  standalone = {
    runner   = wrap {
      name   = "quickspec-standalone-runner";
      script = ''
        #!/usr/bin/env bash
        cat | $*
      '';
    };

    genAnnotatedPkg = wrap {
      name  = "quickspec-standalone-gen-annotated-pkg";
      paths = [ nix nix-config.pipeToNix tipBenchmarks.tools ];
      vars  = {
        NIX_REMOTE = "daemon";
        mkPkg      = wrap {
          name = "quickspec-mk-pkg";
          vars = {
            inherit mkPkgInner;
            NIX_PATH = innerNixPath;
          };
          script = ''
            #!/usr/bin/env bash

            echo "Storing input" 1>&2
            INPUT_TIP=$(pipeToNix input.smt2)
            export INPUT_TIP

            "$mkPkgInner"
          '';
        };
      };

      script = ''
        #!/usr/bin/env bash
        set -e

        echo "Generating package" 1>&2
        OUT_DIR=$(INPUT_TIP="$1" "$mkPkg")
        export OUT_DIR

        echo "Annotating package" 1>&2
        ANNOTATED=$(nix-build --show-trace --no-out-link \
                      --argstr dir "$OUT_DIR"            \
                      -E '{ dir }: with import <nixpkgs> {}; annotated dir')

        jq -n --arg annotated "$ANNOTATED" --arg dir "$OUT_DIR" \
           '{"annotated": $annotated, "out_dir": $dir}'
      '';
    };

    genInput = qsGenerateSig;
  };
};

getCmd = writeScript "getCmd.hs" ''
  #!/usr/bin/env runhaskell
  {-# LANGUAGE OverloadedStrings #-}
  import           Data.Aeson
  import qualified Data.ByteString.Lazy.Char8 as BS
  import           MLSpec.Theory
  import           Language.Eval.Internal

  render ts x = "main = do { eqs <- quickSpecAndSimplify (" ++
                  withoutUndef' (renderWithVariables x ts)  ++
                  "); mapM_ print eqs; }"

  -- Reads JSON from stdin, outputs a QuickSpec signature and associated shell
  -- and Nix commands for running it
  main = do
    projects <- getProjects <$> getContents
    let t = case projects of
                 [t] -> t
                 _   -> error ("Got " ++ show (length projects) ++ " projects")

    rendered <- renderTheory t
    let (ts, x) = case rendered of
                       Nothing      -> error ("Failed to render " ++ show t)
                       Just (ts, x) -> (ts, x)

    BS.putStrLn (encode (object [
        "runner" .= unwords ("runhaskell" : flagsOf x),
        "env"    .= pkgOf x,
        "code"   .= buildInput (render ts) x
      ]))
'';

customHs = writeScript "custom-hs.nix" ''
    # Uses OUT_DIR env var to include the package generated from smtlib data
    (import <nixpkgs> {}).callPackage "${augmentedHs}" {
      hsDir = builtins.getEnv "OUT_DIR";
    }
  '';

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

# Write 'content' to a file, splicing in any shell variables. Add that file to
# the Nix store and put the resulting path in the shell variable 'var'. Like a
# build-time alternative to writeScript.
fileInStore = var: content: ''
  cat << EOF > filed
  ${content}
  EOF
  chmod +x filed
  ${var}=$(nix-store --add filed)
  rm -f filed
'';

qsGenInput = mkGenInput genSig2;

mkGenInput = after: wrap {
  name   = "gen-input";
  paths  = [ bash jq ];
  vars   = {
    inherit after;
    OUT_DIR   = tipBenchmarks.tip-benchmark-haskell;
    ANNOTATED = annotated (toString tipBenchmarks.tip-benchmark-haskell);
    filter = writeScript "filter.jq" ''
      def mkId: {"name": .name, "package": .package, "module": .module};

      def keep($id): $keepers | map(. == $id) | any;

      def setQS: . + {"quickspecable": (.quickspecable and keep(mkId))};

      map(setQS)
    '';
  };
  script = ''
    #!/usr/bin/env bash

    # Sample some names, give the default module and package, then slurp
    # into an array
    echo "Running 'choose_sample $1 $2'" 1>&2
    KEEPERS=$(choose_sample "$1" "$2" |
              jq -R '{"name"    : .,
                      "module"  : "A",
                      "package" : "tip-benchmark-sig"}' |
              jq -s '.')

    # Filters the signature to only those sampled in KEEPERS
    jq --argjson keepers "$KEEPERS" -f "$filter" < "$ANNOTATED" | "$after"
  '';
};

genSig2 = wrap {
  name   = "gen-sig2";
  paths  = [ nix-config.pipeToNix ];
  vars   = {
    NIX_EVAL_HASKELL_PKGS = customHs;
    NIX_PATH              = innerNixPath;
    runGetCmd             = wrap {
      name   = "run-get-cmd";
      paths  = [ (haskellPackages.ghcWithPackages
                   (h: [ h.mlspec h.nix-eval ])) ];
      vars   = {
        inherit getCmd;
      };
      script = ''
        #!/usr/bin/env bash
        runhaskell "$getCmd"
      '';
    };
  };
  script = ''
    #!/usr/bin/env bash
    set -e

    CHOSEN=$(jq 'map(select(.quickspecable))' | pipeToNix)

    "$runGetCmd" < "$CHOSEN" |
      jq --arg chosen "$CHOSEN" '. + { "chosen": $chosen }'
  '';
};

wrapScript = name: script: wrap {
  inherit name script;
  paths = [ env ];
  vars  = {
    LANG                  = "en_US.UTF-8";
    LOCALE_ARCHIVE        = "${glibcLocales}/lib/locale/locale-archive";
    NIX_EVAL_HASKELL_PKGS = customHs;
    NIX_REMOTE            = nixEnv.nixRemote;
    NIX_PATH              = innerNixPath;
  };
};

mkPkgInner = ''
  set -e
  echo "Creating Haskell package" 1>&2
  OUT_DIR=$(nix-build --show-trace --argstr "input" "$INPUT_TIP" \
                      -E 'with import <support> {};
                          { input }:
                          stdenv.mkDerivation {
                            inherit input;
                            name         = "generated-haskell-package";
                            buildInputs  = [ tipBenchmarks.tools ];
                            buildCommand = "
                              mkdir -p \"$out\"
                              OUT_DIR=\"$out\" full_haskell_package < \"$input\"
                            ";
                          }') ||
    ${fail "Failed to create Haskell package"}
  echo "Created Haskell package" 1>&2
'';

innerNixPath =
  "nixpkgs=${toString <nixpkgs>}:support=${toString ../nix-support}";

script = wrapScript "quickspecBench" rawScript;

setUpDir = ''
  [[ -n "$DIR" ]] || {
    echo "No DIR given to work in, using current directory $PWD" 1>&2
    DIR="$PWD"
  }
  export DIR
'';

getInput = ''
  INPUT_TIP=$(pipeToNix)
  echo "Input stored at '$INPUT_TIP'" 1>&2

  # Initialise all of the data we need
  ${mkPkgInner}

  export OUT_DIR

  # Extract ASTs from the Haskell package, annotate and add to the Nix store. By
  # doing this in nix-build, we get content-based caching for free.
     STORED=$(nix-store --add "$OUT_DIR")
       EXPR="with import <support> {}; annotated \"$STORED\""
  ANNOTATED=$(nix-build --show-trace -E "$EXPR")

  export ANNOTATED
'';

rawScript = writeScript "quickspec-bench" ''
  #!/usr/bin/env bash
  set -e

  ${setUpDir}
  ${getInput}

  # Explore
  if [[ -n "$SAMPLE_SIZES" ]]
  then
    # The numeric arguments are arbitrary
    echo "Running sampler to obtain environment" 1>&2
    export NIXENV=$("${qsGenInput}" 5 1 | jq -r '.env')

    echo "Looping through sample sizes" 1>&2
    for SAMPLE_SIZE in $SAMPLE_SIZES
    do
      echo "Limiting to a sample size of '$SAMPLE_SIZE'" 1>&2

      export      INFO="$SAMPLE_SIZE"
      export GEN_INPUT="${qsGenInput}"
      export       CMD="${writeScript "run-cmd" ''
                            #!/usr/bin/env bash
                            INPUT=$(cat)
                            RUNNER=$(echo "$INPUT" | jq -r '.runner')
                            HASKELL_PROGRAM_CODE=$(echo "$INPUT" | jq -r '.code')

                            if [[ -n "$EXPLORATION_MEM" ]]
                            then
                              echo "Limiting memory to '$EXPLORATION_MEM'" 1>&2
                              export MAX_KB="$EXPLORATION_MEM"
                            fi
                            echo "$HASKELL_PROGRAM_CODE" | "${timeout}/bin/withTimeout" $RUNNER
                          ''}"

      benchmark
    done
  else
    echo "No sample size given, using whole signature" 1>&2
    OUTPUT=$("${genSig2}" < "$ANNOTATED")

    export CMD=$(echo "$OUTPUT" | jq -r '.runner')
    export HASKELL_PROGRAM_CODE=$(echo "$OUTPUT" | jq -r '.code')
    export GEN_INPUT="${writeScript "run-code" ''echo "$HASKELL_PROGRAM_CODE"''}"

    export NIXENV=$(echo "$OUTPUT" | jq -r '.env')
    INFO="" benchmark
  fi
'';

env = buildEnv {
  name  = "te-env";
  paths = [ benchmark jq nix tipBenchmarks.tools ];
};

qs = stdenv.mkDerivation (withNix {
  name = "quickspecBench";
  src  = script;
  buildInputs  = [ env ];
  unpackPhase  = "true";  # Nothing to do

  doCheck    = true;
  checkPhase = with rec {
    test = name: code: ''
      echo "Testing ${name}" 1>&2
      bash "${writeScript "quickspec-${name}-test" code}" || {
        echo "Test ${name} failed" 1>&2
        exit 1
      }
      echo "Passed ${name}" 1>&2
    '';

  }; ''
    ${test "test-gen-input" ''
      P=$(${qsGenInput} 4 2) || ${fail "Couldn't run gen-input"}
    ''}
    ${test "test-gen-haskell" ''
      C=$(${qsGenInput} 4 2 | jq 'has("code")') || ${fail "Failed to gen"}
      [[ "$C" = "true" ]] || ${fail "Didn't gen Haskell ($C)"}
    ''}
    ${test "check-garbage" ''
      if echo '!"£$%^&*()' | "$src" 1> /dev/null 2> garbage.err
      then
        cat garbage.err 1>&2
        ${fail "Shouldn't have accepted garbage"}
      fi
    ''}
    ${test "test-can-run-quickspecbench" ''
      BENCH_OUT=$(DIR="$PWD" "$src" < "${../tests/example.smt2}") ||
        ${fail "Failed to run.\n$BENCH_OUT"}

      RESULTS=$(echo "$BENCH_OUT" | jq '.results | length') ||
        ${fail "No results"}

      [[ "$RESULTS" -gt 0 ]] || ${fail "Empty results"}

      NOFAILS=$(echo "$BENCH_OUT" |
                jq '.results | map(.failure == null) | all') ||
        ${fail "Couldn't check for failures"}

      [[ "$NOFAILS" = "true" ]] || ${fail "Encountered failures"}

      while read -r F
      do
        [[ -e "$F" ]] || ${fail "Couldn't find stdout file"}

        EQS=$(grep -v "^Depth" < "$F" | jq -s '. | length') ||
          ${fail "Couldn't get equations from stdout"}

        [[ "$EQS" -gt 0 ]] || ${fail "Found no equations"}
      done < <(echo "$BENCH_OUT" | jq -r '.results | .[] | .stdout')
    ''}
  '';

  installPhase = ''
    mkdir -p "$out/bin"
    cp "$src" "$out/bin/quickspecBench"
  '';
});

}
