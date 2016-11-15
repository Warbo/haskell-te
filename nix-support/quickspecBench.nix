{ ensureVars, glibcLocales, haskellPackages, jq, lib, tipBenchmarks,
  writeScript }:

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
    [t]          <- getProjects <$> getContents
    Just (ts, x) <- renderTheory t
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
  let hsName = "tip-benchmark-sig";  # The name used by full_haskell_package.rkt
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
# the Nix store and put the resulting path in the shell variable 'var'
fileInStore = var: content: ''
  cat << EOF > filed
  ${content}
  EOF
  chmod +x filed
  ${var}=$(nix-store --add filed)
  rm -f filed
'';

mkQuickSpecSig = ''
  [[ -z "$SIG" ]] || return 0

  ${getAsts}
  ${ensureVars ["DIR" "OUT_DIR" "ANNOTATED"]}

  SIG="$DIR"
  export SIG
  mkdir -p "$SIG"
  pushd "$SIG" > /dev/null

  NIX_EVAL_HASKELL_PKGS="${customHs}"
  export NIX_EVAL_HASKELL_PKGS

  OUTPUT=$(nix-shell \
    -p '(haskellPackages.ghcWithPackages (h: [ h.mlspec h.nix-eval ]))' \
    --show-trace --run 'runhaskell ${mkSigHs}' < "$ANNOTATED")

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
    # If an AST doesn't appear in BENCH_FILTER_KEEPERS, mark it as not quickspecable
    "${jq}/bin/jq" --argjson keepers "$BENCH_FILTER_KEEPERS" -f "${filter}"
  fi
'';

mkDir = ''
  [[ -z "$DIR" ]] || return 0

  OUR_DIR=$(mktemp -d --tmpdir "quickspecBenchXXXXX")
  DIR="$OUR_DIR"
'';

mkPkgInner = ''
  ${ensureVars ["DIR"]}

  export OUT_DIR="$DIR/hsPkg"
  mkdir -p "$OUT_DIR"

  echo "Creating Haskell package" 1>&2
  "${tipBenchmarks.tools}/bin/full_haskell_package.rkt"
  echo "Created Haskell package" 1>&2

  OUT_DIR=$(nix-store --add "$OUT_DIR")
'';

mkPkg = ''
  [[ -z "$OUT_DIR" ]] || return 0

  ${mkDir}
  ${mkPkgInner}
'';

# Use ./.. so all of our dependencies are included
getAsts = ''
  [[ -z "$ANNOTATED" ]] || return 0

  ${mkPkg}
  ${ensureVars ["DIR" "OUT_DIR"]}

  ANNOTATED="$DIR/annotated.json"
  STORED=$(nix-store --add "$OUT_DIR")
    EXPR="with import ${./..}/nix-support {}; annotated \"$STORED\""
       F=$(nix-build --show-trace -E "$EXPR")
  "${filterSample}" < "$F" | "${jq}/bin/jq" 'map(select(.quickspecable))' > "$ANNOTATED"
'';

runSig = ''
  [[ -z "$RESULT" ]] || return 0

  ${mkQuickSpecSig}
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
  [[ -z "$JSON_OUT" ]] || return 0

  ${runSig}
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

  ${mkJson}

  cat "$JSON_OUT"
'';

}
