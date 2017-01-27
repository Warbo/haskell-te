{ buildEnv, ensureVars, glibcLocales, haskellPackages, jq, lib, makeWrapper,
  stdenv, tipBenchmarks, withNix, writeScript }:

# Provide a script which accepts smtlib data, runs it through QuickSpec and
# outputs the resulting equations along with benchmark times. The script should
# be runnable from the commandline, as long as the haskell-te package is in PATH

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

mkQuickSpecSig = ''
  [[ -n "$ANNOTATED" ]] || {
    ${getAsts}
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
    "${jq}/bin/jq" --argjson keepers "$BENCH_FILTER_KEEPERS" -f "${filter}"
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
  env
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

# Use ./.. so all of our dependencies are included
getAsts = ''
  [[ -n "$OUT_DIR" ]] || {
    ${mkPkg}
  }
  ${ensureVars ["DIR" "OUT_DIR"]}

  ANNOTATED="$DIR/annotated.json"
  STORED=$(nix-store --add "$OUT_DIR")
    EXPR="with import ${./..}/nix-support {}; annotated \"$STORED\""
       F=$(nix-build --show-trace -E "$EXPR")
  "${filterSample}" < "$F" | "${jq}/bin/jq" 'map(select(.quickspecable))' > "$ANNOTATED"
'';

runSig = ''
  [[ -n "$SIG" ]] || {
    ${mkQuickSpecSig}
  }
  ${ensureVars ["DIR" "BENCH_COMMAND" "RUN_COMMAND"]}

  RESULT="$DIR/eqs"
  "$RUN_COMMAND" | grep -v '^Depth' | "${jq}/bin/jq" -s '.' > "$RESULT"

  if [[ "$DO_BENCH" -eq 1 ]]
  then
    "$BENCH_COMMAND"
  else
    echo "Not benchmarking. To benchmark, set DO_BENCH env var to 1" 1>&2
    echo '"Not benchmarked"' > "$TIME_JSON"
  fi
'';

mkJson = ''
  [[ -n "$RESULT" ]] || {
    ${runSig}
  }
  ${ensureVars ["DIR" "TIME_JSON" "RESULT"]}

  JSON_OUT="$DIR/out.json"

  "${jq}/bin/jq" -n --slurpfile time   "$TIME_JSON" \
                    --slurpfile result "$RESULT"    \
                    '{"time": $time, "result": $result}' > "$JSON_OUT" || {
    echo -e "START TIME_JSON\n$(cat "$TIME_JSON")\nEND TIME_JSON" 1>&2
    echo -e "START RESULT   \n$(cat "$RESULT")   \nEND RESULT"    1>&2
    exit 1
  }
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

  [[ -n "$JSON_OUT" ]] || {
    ${mkJson}
  }

  cat "$JSON_OUT"
'';

env = buildEnv {
  name  = "te-env";
  paths = [ tipBenchmarks.tools ];
};

qs = stdenv.mkDerivation (withNix {
  name = "quickspecBench";
  src  = script;
  buildInputs  = [ env makeWrapper ];
  unpackPhase  = "true";  # Nothing to do

  doCheck    = true;
  checkPhase = with rec {
    #run = code: ''
    #  DIR="$PWD" source ${writeScript "to-run" code} < ${../tests/example.smt2}
    #'';
    test = name: code: ''
      bash "${writeScript "quickspec-${name}-test" code}" || {
        echo "Test ${name} failed" 1>&2
        exit 1
      }
    '';
    checkVar = var: ''
      [[ -n "${"$" + var}" ]] || {
        echo "No ${var}" 1>&2
        exit 1
      }
      [[ -e "${"$" + var}" ]] || {
        echo "${var} '${"$" + var}' doesn't exist" 1>&2
        exit 1
      }
    '';
  }; ''
    ${test "check-garbage" ''
      if echo '!"£$%^&*()' | "$src" 1>/dev/null 2>/dev/null
      then
        exit 1
      fi
    ''}
    ${test "can-run-quickspecbench" ''
      "$src" < ${./example.smt2} > /dev/null || exit 1
      ${checkVar "RESULT"}
      ${checkVar "SIG"}
      ${checkVar "ANNOTATED"}
      ${checkVar "OUT_DIR"}
      ${checkVar "DIR"}
    ''}
    ${test "generate-signature" ''
      export   OUT_DIR="${../tests/testPackage}"
      export ANNOTATED="${../tests/annotated.json}"
      export       DIR="$PWD"
      "$src" < ${../tests/example.smt2}

      for F in sig.hs env.nix
      do
        [[ -e "$F" ]] || {
          echo "Couldn't find '$F'" 1>&2
          exit 1
        }
      done
    ''}
    ${test "get-json-output" ''
      BENCH_OUT=$("$src" < "${./example.smt2}") || exit 1

      TYPE=$(echo "$BENCH_OUT" | jq -r 'type') || {
        echo -e "START BENCH_OUT\n\n$BENCH_OUT\n\nEND BENCH_OUT" 1>&2
        exit 1
      }

      [[ "x$TYPE" = "xobject" ]] || {
        echo -e "START BENCH_OUT\n\n$BENCH_OUT\n\nEND BENCH_OUT" 1>&2
        echo "'$TYPE' is not object" 1>&2
        exit 1
      }
    ''}
    ${test "filter-samples" (let keepers = [
      { name = "append";          module = "A"; package = "tip-benchmark-sig"; }
      { name = "constructorNil";  module = "A"; package = "tip-benchmark-sig"; }
      { name = "constructorCons"; module = "A"; package = "tip-benchmark-sig"; }
    ]; in ''
      set -e
      export BENCH_FILTER_KEEPERS='${toJSON keepers}'
      BENCH_OUT=$(quickspecBench < ${../benchmarks/list-full.smt2})
      for S in append constructorNil constructorCons
      do
        echo "$BENCH_OUT" | jq '.result' | grep "$S" > /dev/null || {
          echo "No equations for '$S'" 1>&2
          exit 1
        }
      done
      for S in map foldl foldr length reverse
      do
        if echo "$BENCH_OUT" | jq '.result' | grep "$S" > /dev/null
        then
          echo "Found equation with forbidden symbol '$S'" 1>&2
          exit 1
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
