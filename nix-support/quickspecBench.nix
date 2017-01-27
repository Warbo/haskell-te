{ buildEnv, ensureVars, glibcLocales, haskellPackages, jq, lib, makeWrapper,
  stdenv, tipBenchmarks, withNix, writeScript }:

# Provides a script which accepts smtlib data, runs it through QuickSpec and
# outputs the resulting equations along with benchmark times.

# Note that we use "./.." so that all of our dependencies get included

with builtins; with lib;

rec {

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

mkDir = ''
  OUR_DIR=$(mktemp -d --tmpdir "quickspecBenchXXXXX")
  DIR="$OUR_DIR"
'';

mkPkgInner = ''
  ${ensureVars ["DIR"]}
  set -e
  export OUT_DIR="$DIR/hsPkg"
  mkdir -p "$OUT_DIR"

  echo "Creating Haskell package" 1>&2
  full_haskell_package || exit 1
  echo "Created Haskell package" 1>&2

  OUT_DIR=$(nix-store --add "$OUT_DIR")
'';

mkPkg = ''
  [[ -n "$DIR" ]] || {
    ${mkDir}
  }
  ${mkPkgInner}
'';

script = writeScript "quickspec-bench" ''
  #!/usr/bin/env bash
  set -e

  function cleanup {
    if [[ -n "$OUR_DIR" ]] && [[ -d "$OUR_DIR" ]]
    then
      rm -rf "$OUR_DIR"
    fi
  }
  trap cleanup EXIT

  [[ -n "$RESULT" ]] || {
    [[ -n "$SIG"  ]] || {
      [[ -n "$ANNOTATED" ]] || {
        [[ -n "$OUT_DIR" ]] || {
          ${mkPkg}
        }
        ${ensureVars ["DIR" "OUT_DIR"]}

        ANNOTATED="$DIR/annotated.json"
           STORED=$(nix-store --add "$OUT_DIR")
             EXPR="with import ${./..}/nix-support {}; annotated \"$STORED\""
                F=$(nix-build --show-trace -E "$EXPR")
        "${filterSample}" < "$F" | jq 'map(select(.quickspecable))' > "$ANNOTATED"
      }
      ${ensureVars ["DIR" "OUT_DIR" "ANNOTATED"]}

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

      echo "$OUTPUT" | tail -n +3 > sig.hs
      HS=$(nix-store --add sig.hs)

      TIME_JSON="$DIR/time.json"

      CMD=$(echo "$OUTPUT" | head -n1 | tr -d '\n')

      ${fileInStore "RH" ''
        export LANG='en_US.UTF-8'
        export LOCALE_ARCHIVE='${glibcLocales}/lib/locale/locale-archive'
        $CMD < $HS
      ''}

      ${fileInStore "B" ''
        export LANG='en_US.UTF-8'
        export LOCALE_ARCHIVE=${glibcLocales}/lib/locale/locale-archive
        "${haskellPackages.bench}/bin/bench" --template json --output "$TIME_JSON" "$RH" 1>&2
      ''}

      WRAP="export NIX_EVAL_HASKELL_PKGS='$NIX_EVAL_HASKELL_PKGS'
      export OUT_DIR='$OUT_DIR'
      nix-shell --show-trace -p '(import $E)' --run"

      ${fileInStore "BENCH_COMMAND" ''
        $WRAP "$B"
      ''}

      ${fileInStore "RUN_COMMAND" ''
        $WRAP "$RH"
      ''}

      popd > /dev/null
    }
    ${ensureVars ["DIR" "BENCH_COMMAND" "RUN_COMMAND"]}

    RESULT="$DIR/eqs"
    "$RUN_COMMAND" | grep -v '^Depth' | jq -s '.' > "$RESULT"

    if [[ "$DO_BENCH" -eq 1 ]]
    then
      "$BENCH_COMMAND"
    else
      echo "Not benchmarking. To benchmark, set DO_BENCH env var to 1" 1>&2
      echo '"Not benchmarked"' > "$TIME_JSON"
    fi
  }
  ${ensureVars ["DIR" "TIME_JSON" "RESULT"]}

  jq -n --slurpfile time   "$TIME_JSON" \
        --slurpfile result "$RESULT"    \
        '{"time": $time, "result": $result}' || {
    echo -e "START TIME_JSON\n$(cat "$TIME_JSON")\nEND TIME_JSON" 1>&2
    echo -e "START RESULT   \n$(cat "$RESULT")   \nEND RESULT"    1>&2
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
    '';
    fail = msg: ''{ echo -e "${msg}" 1>&2; exit 1; }'';
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
