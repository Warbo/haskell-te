{ buildEnv, ensureVars, glibcLocales, haskellPackages, jq, lib, makeWrapper,
  stdenv, time, tipBenchmarks, withNix, writeScript }:

# Provides a script which accepts smtlib data, runs it through QuickSpec and
# outputs the resulting equations along with benchmark times.

# Note that we use "./.." so that all of our dependencies get included

with builtins; with lib;

rec {

fail = msg: ''{ echo -e "${msg}" 1>&2; exit 1; }'';

mkSigHs = writeScript "mkSig.hs" ''
  {-# LANGUAGE OverloadedStrings #-}
  import MLSpec.Theory
  import Language.Eval.Internal

  render ts x = "main = do { eqs <- quickSpecAndSimplify (" ++
                  withoutUndef' (renderWithVariables x ts)  ++
                  "); mapM_ print eqs; }"

  -- Reads JSON from stdin, outputs a QuickSpec signature and associated shell
  -- and Nix commands for running it
  main = do
    [t]      <- getProjects <$> getContents
    rendered <- renderTheory t
    let (ts, x) = case rendered of
                       Nothing      -> error ("Failed to render " ++ show t)
                       Just (ts, x) -> (ts, x)
    let f = render ts
    putStrLn . unwords . ("runhaskell":) . flagsOf $ x
    putStrLn (pkgOf   x)
    putStrLn (buildInput f x)
'';

customHs = writeScript "custom-hs.nix" ''
  # Provides a set of Haskell packages for use by nix-eval. Uses OUT_DIR env var
  # to include the package generated from smtlib data
  with import ${./..}/nix-support {};
  with builtins;
  let hsName = "tip-benchmark-sig";  # The name used by full_haskell_package
      hsDir  = getEnv "OUT_DIR";
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

filterSample = let filter = writeScript "filter.jq" ''
    def mkId: {"name": .name, "package": .package, "module": .module};

    def keep($id): $keepers | map(. == $id) | any;

    def setQS: . + {"quickspecable": (.quickspecable and keep(mkId))};

    map(setQS)
  '';
in writeScript "filterSample.sh" ''
  #!/usr/bin/env bash
  if [[ -z "$BENCH_FILTER_KEEPERS" ]]
  then
    cat
  else
    # If an AST's not in BENCH_FILTER_KEEPERS, mark it as not quickspecable
    jq --argjson keepers "$BENCH_FILTER_KEEPERS" -f "${filter}"
  fi
'';

mkPkgInner = ''
  ${ensureVars ["DIR"]}
  set -e
  export OUT_DIR="$DIR/hsPkg"
  if [[ -d "$OUT_DIR" ]]
  then
    echo "Haskell output directory $OUT_DIR exists; aborting" 1>&2
    exit 1
  fi

  mkdir -p "$OUT_DIR"

  echo "Creating Haskell package" 1>&2
  full_haskell_package < "$INPUT_TIP" ||
    ${fail "Failed to create Haskell package"}
  echo "Created Haskell package" 1>&2
  OUT_DIR=$(nix-store --add "$OUT_DIR")
'';

script = writeScript "quickspec-bench" ''
  #!/usr/bin/env bash
  set -e

  [[ -n "$DIR" ]] || {
    echo "No DIR given to work in, using current directory $PWD" 1>&2
    DIR="$PWD"
  }

  echo "Checking for input" 1>&2
  if [[ -t 0 || -p /dev/stdin ]]
  then
    echo "stdin is a tty; assuming we have no input" 1>&2
    GIVEN_INPUT=0
  else
    # Shell is non-interactive; it's safe to try cat
    cat > "$DIR/stdin"
    if [[ -s "$DIR/stdin" ]]
    then
      echo "Input found on stdin" 1>&2
      GIVEN_INPUT=1
      INPUT_TIP=$(nix-store --add "$DIR/stdin")
      echo "Input stored at '$INPUT_TIP'" 1>&2
    else
      echo "No input found on stdin" 1>&2
      rm "$DIR/stdin"
      GIVEN_INPUT=0
    fi
  fi

  if [[ "$GIVEN_INPUT" -eq 0 ]]
  then
    echo "Preparing to use TIP benchmarks"
    OUT_DIR="${tipBenchmarks.tip-benchmark-haskell}"
  else
    ${mkPkgInner}
  fi

  # By adding things to the Nix store, we get content-based caching; nix-build
  # will check whether these ASTs have already been annotated and use that if so
  STORED=$(nix-store --add "$OUT_DIR")
    EXPR="with import ${./..}/nix-support {}; annotated \"$STORED\""
       F=$(nix-build --show-trace -E "$EXPR")

  # Check for incompatible options
  if [[ -n "$SAMPLE_SIZE" ]] && [[ "$GIVEN_INPUT" -eq 1 ]]
  then
    {
      echo "Error: data given on stdin, and asked to draw samples. These"
      echo "options are incompatible: sampling will only work for the TIP"
      echo "benchmarks. Either avoid the SAMPLE_SIZE option, to use all of"
      echo "the given input; otherwise avoid giving data on stdin, to use the"
      echo "TIP benchmarks for sampling."
    } 1>&2
    exit 1
  fi
  if [[ -n "$BENCH_FILTER_KEEPERS" ]] && [[ -n "$SAMPLE_SIZE" ]]
  then
    echo "Can't use BENCH_FILTER_KEEPERS and SAMPLE_SIZE at the same time" 1>&2
    exit 1
  fi

  # Impose any restrictions to our annotated ASTs
  if [[ -n "$BENCH_FILTER_KEEPERS" ]]
  then
    echo "Limiting to the given subset of symbols" 1>&2
    ANNOTATED="$DIR/annotated.given_sample.json"
    "${filterSample}" < "$F" | jq 'map(select(.quickspecable))' > "$ANNOTATED"
  elif [[ -n "$SAMPLE_SIZE" ]]
  then
    echo "Limiting to a sample size of '$SAMPLE_SIZE'" 1>&2
    echo "FIXME: Different annotations for different samples" 1>&2
    choose_sample "$SAMPLE_SIZE" 0 1>&2
    exit 1
    ANNOTATED="$DIR/annotated.$SAMPLE_SIZE.json"
    "${filterSample}" < "$F" | jq 'map(select(.quickspecable))' > "$ANNOTATED"
  else
    echo "No sample size given, using whole signature" 1>&2
    ANNOTATED="$DIR/annotated.json"
    jq 'map(select(.quickspecable))' > "$ANNOTATED" < "$F" > "$ANNOTATED"
  fi

  SIG="$DIR"
  export SIG
  mkdir -p "$SIG"
  pushd "$SIG" > /dev/null

  NIX_EVAL_HASKELL_PKGS="${customHs}"
  export NIX_EVAL_HASKELL_PKGS

  OUTPUT=$(nix-shell \
    -p '(haskellPackages.ghcWithPackages (h: [ h.mlspec h.nix-eval ]))' \
    --show-trace --run 'runhaskell ${mkSigHs}' < "$ANNOTATED" | tee mkSigHs.stdout)

  [[ -n "$OUTPUT" ]] || {
    echo "Failed to make signature"
    exit 1
  }

  echo "$OUTPUT" | head -n2 | tail -n1 > env.nix
  E=$(nix-store --add env.nix)

  echo "$OUTPUT" | tail -n +3 > "$DIR/sig.hs"

  TIME_JSON="$DIR/time.json"

  CMD=$(echo "$OUTPUT" | head -n1 | tr -d '\n')
  export CMD

  popd > /dev/null

  ${ensureVars ["DIR" "CMD"]}

  cat << EOF > command.sh
  #!/usr/bin/env bash
  $CMD < "$DIR/sig.hs"
  EOF

  chmod +x command.sh

  export OUT_DIR
  export NIX_EVAL_HASKELL_PKGS
  export LANG='en_US.UTF-8'
  export LOCALE_ARCHIVE='${glibcLocales}/lib/locale/locale-archive'
  export DIR

  echo "FIXME: sampling and looping should go here somewhere" 1>&2
  nix-shell --show-trace -p "(import $E)" \
            --run '${time}/bin/time -o time -f "%e" \
                     ./command.sh 1> stdout 2> >(tee stderr 1>&2)'
  [[ -e time   ]] || ${fail "No time file found"  }
  [[ -e stdout ]] || ${fail "No stdout file found"}
  [[ -e stderr ]] || ${fail "No stderr file found"}

  echo "Extracting equations from output" 1>&2
  grep -v '^Depth' < stdout | jq -s '.' > "$DIR/eqs"

  echo "Extracting times" 1>&2
  cat < time > "$DIR/time.json"

  jq -n --slurpfile time   "$DIR/time.json" \
        --slurpfile result "$DIR/eqs"       \
        '{"time": $time, "result": $result}' || {
    echo -e "START TIME_JSON\n$(cat "$TIME_JSON")\nEND TIME_JSON" 1>&2
    echo -e "START RESULT   \n$(cat "$DIR/eqs")   \nEND RESULT"    1>&2
    exit 1
  }
'';

env = buildEnv {
  name  = "te-env";
  paths = [ jq tipBenchmarks.tools ];
};

qs = stdenv.mkDerivation (withNix {
  name = "quickspecBench";
  src  = script;
  buildInputs  = [ env makeWrapper ];
  unpackPhase  = "true";  # Nothing to do

  doCheck    = true;
  checkPhase = with rec {
    test = name: code: ''
      bash "${writeScript "quickspec-${name}-test" code}" || {
        echo "Test ${name} failed" 1>&2
        exit 1
      }
      if [[ -d ./hsPkg ]]; then rm -r ./hsPkg; fi
    '';

  }; ''
    ${test "check-garbage" ''
      if echo '!"£$%^&*()' | "$src" 1>/dev/null 2>/dev/null
      then
        ${fail "Shouldn't have accepted garbage"}
      fi
    ''}
    ${test "can-run-quickspecbench" ''
      BENCH_OUT=$(DIR="$PWD" "$src" < "${../tests/example.smt2}") || exit 1

      [[ -e ./eqs            ]] || ${fail "No eqs found"           }
      [[ -e ./env.nix        ]] || ${fail "No env.nix found"       }
      [[ -e ./sig.hs         ]] || ${fail "No sig.hs found"        }
      [[ -e ./annotated.json ]] || ${fail "No annotated.json found"}
      [[ -d ./hsPkg          ]] || ${fail "No hsPkg found"         }

      TYPE=$(echo "$BENCH_OUT" | jq -r 'type') ||
        ${fail "START BENCH_OUT\n\n$BENCH_OUT\n\nEND BENCH_OUT"}

      [[ "x$TYPE" = "xobject" ]] ||
        ${fail ''START BENCH_OUT\n\n$BENCH_OUT\n\nEND BENCH_OUT
                 '$TYPE' is not object''}
    ''}
    ${test "filter-samples" ''
      set -e
      export BENCH_FILTER_KEEPERS='${toJSON [
        { name = "append";          module = "A"; package = "tip-benchmark-sig"; }
        { name = "constructorNil";  module = "A"; package = "tip-benchmark-sig"; }
        { name = "constructorCons"; module = "A"; package = "tip-benchmark-sig"; }
      ]}'
      BENCH_OUT=$("$src" < ${../benchmarks/list-full.smt2})
      for S in append constructorNil constructorCons
      do
        echo "$BENCH_OUT" | jq '.result' | grep "$S" > /dev/null ||
          ${fail "No equations for '$S'"}
      done
      for S in map foldl foldr length reverse
      do
        if echo "$BENCH_OUT" | jq '.result' | grep "$S" > /dev/null
        then
          echo -e "BENCH_OUT:\n$BENCH_OUT\nEND_BENCH_OUT" 1>&2
          ${fail "Found equation with forbidden symbol '$S'"}
        fi
      done
    ''}
  '';

  installPhase = ''
    mkdir -p "$out/bin"
    makeWrapper "$src" "$out/bin/quickspecBench" \
      --prefix PATH : "${env}/bin"
  '';
});

}
