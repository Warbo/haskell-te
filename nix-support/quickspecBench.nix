{ annotated, bash, checkStderr, buildEnv, ensureVars, fail, glibcLocales,
  haskellPackages, inNixedDir, jq, lib, makeWrapper, nix, nix-config, nixEnv,
  pipeToNix, runCmd, runCommand, stdenv, time, timeout, tipBenchmarks, withNix,
  wrap, writeScript }:

# Provides a script which accepts smtlib data, runs it through QuickSpec and
# outputs the resulting equations

with builtins; with lib;

rec {

qsGenerateSig =
  with rec {
    runGetCmd = wrap {
      name  = "quickspec-run-gen-cmd";
      file  = getCmd;
      paths = [
        nix
        (haskellPackages.ghcWithPackages (h: [ h.mlspec h.nix-eval ]))
      ];
      vars  = nixEnv // {
        #NIX_PATH = innerNixPath;
        NIX_EVAL_HASKELL_PKGS = customHs;
      };
    };
  };
  wrap {
    name   = "quickspec-generate-sig";
    paths  = [ jq ];
    vars   = { inherit runGenCmd; };
    script = ''
      #!/usr/bin/env bash
      jq 'map(select(.quickspecable))' | "$runGetCmd"
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
      paths = [ nix ];
      vars  = nixEnv // {
        mkPkg      = wrap {
          name  = "quickspec-mk-pkg";
          paths = [ pipeToNix ];
          vars  = nixEnv // {
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
  paths  = [ bash jq tipBenchmarks.tools ];
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
  paths  = [ pipeToNix ];
  vars   = nixEnv // {
    NIX_EVAL_HASKELL_PKGS = customHs;
    NIX_PATH              = innerNixPath;
    runGetCmd             = wrap {
      name   = "run-get-cmd";
      paths  = [
        nix
        (haskellPackages.ghcWithPackages (h: [ h.mlspec h.nix-eval ]))
      ];
      vars   = nixEnv // { inherit getCmd; };
      script = ''
        #!/usr/bin/env bash
        exec runhaskell "$getCmd"
      '';
    };
  };
  script = ''
    #!/usr/bin/env bash
    set -e

    CHOSEN=$(jq 'map(select(.quickspecable))' | pipeToNix quickspec-asts.json)

    "$runGetCmd" < "$CHOSEN" |
      jq --arg chosen "$CHOSEN" '. + { "chosen": $chosen }'
  '';
};

wrapScript = name: script: wrap {
  inherit name script;
  paths = [ env ];
  vars  = nixEnv // {
    LANG                  = "en_US.UTF-8";
    LOCALE_ARCHIVE        = "${glibcLocales}/lib/locale/locale-archive";
    NIX_EVAL_HASKELL_PKGS = customHs;
    NIX_PATH              = innerNixPath;
  };
};

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
    [[ -n "$INPUT_TIP" ]] || {
      echo "No INPUT_TIP given, aborting" 1>&2
      exit 1
    }
    echo "Creating Haskell package" 1>&2
    inNixedDir "$MAKE_PACKAGE" "generated-haskell-package" ||
      fail "Failed to create Haskell package"
    echo "Created Haskell package" 1>&2
  '';
};

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
  export INPUT_TIP

  echo "Input stored at '$INPUT_TIP'" 1>&2

  # Initialise all of the data we need
  OUT_DIR=$("$mkPkgInner")

  export OUT_DIR

  # Extract ASTs from the Haskell package, annotate and add to the Nix store. By
  # doing this in nix-build, we get content-based caching for free.
     STORED=$(nix-store --add "$OUT_DIR")
       EXPR="with import <support> {}; annotated \"$STORED\""
  ANNOTATED=$(nix-build --show-trace -E "$EXPR")

  export ANNOTATED
'';

env = buildEnv {
  name  = "te-env";
  paths = [ jq nix tipBenchmarks.tools ];
};

qs = nix-config.withDeps checks qsRaw;

qsRaw = nix-config.attrsToDirs {
  bin = {
    quickspec = wrap {
      name  = "quickspec-bench";
      paths = [ bash jq nix pipeToNix ];
      vars  = nixEnv // {
        inherit checkStderr genSig2 mkPkgInner;
        LANG                  = "en_US.UTF-8";
        LOCALE_ARCHIVE        = "${glibcLocales}/lib/locale/locale-archive";
        NIX_EVAL_HASKELL_PKGS = customHs;
        NIX_PATH              = innerNixPath;
      };
      script = ''
        #!/usr/bin/env bash
        set -e

        ${setUpDir}
        ${getInput}

        OUTPUT=$("$genSig2" < "$ANNOTATED")

        HASKELL_PROGRAM_CODE=$(echo "$OUTPUT" | jq -r '.code'  )
                      NIXENV=$(echo "$OUTPUT" | jq -r '.env'   )
                         CMD=$(echo "$OUTPUT" | jq -r '.runner')

        function run() {
          if [[ -n "$NIXENV" ]]
          then
            nix-shell -p "$NIXENV" --run "'$CMD'"
          else
            "$CMD" "$HASKELL_PROGRAM_CODE"
          fi
        }

        echo "$HASKELL_PROGRAM_CODE" | run 2> >("$checkStderr")
      '';
    };
  };
};

checks =
  with {
    test = name: code: runCommand "quickspec-${name}-test"
      {
        given       = name;
        buildInputs = [ fail jq pipeToNix qsRaw ];
      }
      ''
        #!/usr/bin/env bash
        set -e
        {
          ${code}
        } || exit 1
        echo "pass" > "$out"
      '';
  };
  [
    (test "gen-input" "${qsGenInput} 4 2 > /dev/null")

    (test "gen-haskell" ''
      C=$(${qsGenInput} 4 2 | jq 'has("code")') || fail "Failed to gen"
      [[ "$C" = "true" ]] || fail "Didn't gen Haskell ($C)"
    '')

    (test "check-garbage" ''
      if echo '!"£$%^&*()' | quickspec 1> /dev/null 2> garbage.err
      then
        cat garbage.err 1>&2
        fail "Shouldn't have accepted garbage"
      fi
    '')

    (test "can-run-quickspecbench" ''
      BENCH_OUT=$(DIR="$PWD" quickspec < "${../tests/example.smt2}" |
                  pipeToNix) ||
        fail "Failed to run.\n$BENCH_OUT"

      echo "Cached to $BENCH_OUT" 1>&2

      RESULTS=$(jq 'length' < "$BENCH_OUT") ||
        fail "Couldn't get equation array"

      [[ "$RESULTS" -gt 0 ]] || fail "Found no equations"
    '')
  ];

}
