{ ensureVars, glibcLocales, jq, lib, tipBenchmarks, writeScript }:

# Provide a script which accepts smtlib data, runs it through QuickSpec and
# outputs the resulting equations along with benchmark times. The script should
# be runnable from the commandline, as long as the haskell-te package is in PATH

with builtins; with lib;

rec {

mkSigHs = writeScript "mkSig.hs" ''
  {-# LANGUAGE OverloadedStrings #-}
  import MLSpec.Theory
  import Language.Eval.Internal

  render ts x = "main = do { quickSpecAndSimplify (" ++ withoutUndef' (renderWithVariables x ts) ++ ") }"

  -- Reads JSON from stdin, outputs a QuickSpec signature and associated shell
  -- and Nix commands for running it
  main = do
    [t]     <- getProjects <$> getContents
    (ts, x) <- renderTheory t
    let f = render ts
        y = withPkgs ["bench"] x
    putStrLn . unwords . ("runhaskell":) . flagsOf $ y
    putStrLn (pkgOf   y)
    putStrLn (buildInput f y)
'';

customHs = writeScript "custom-hs.nix" ''
  # Provides a set of Haskell packages for use by nix-eval. Uses env vars
  # HASKELL_NAME and OUT_DIR to include the package generated from smtlib data
  with import ${./..}/nix-support {};
  with builtins;
  let hsName = getEnv "HASKELL_NAME";
      hsDir  = getEnv "OUT_DIR";
      hsPkgs = haskellPackages.override {
        overrides = self: super:
          # Include existing overrides, along with our new one
          hsOverride self super // listToAttrs [{
            name  = hsName;
            value = self.callPackage (import (nixedHsPkg hsDir null)) {};
          }];
      };
      # Echo "true", with our Haskell package as a dependency
      check = stdenv.mkDerivation {
        name = "check-for-pkg";
        buildInputs  = [(hsPkgs.ghcWithPackages (h: [h."''${hsName}"]))];
        buildCommand = "source $stdenv/setup; echo true > $out";
      };
   in assert hsName != ""           || abort "Got no HASKELL_NAME";
      assert hsDir  != ""           || abort "Got no OUT_DIR";
      assert hsPkgs ? "''${hsName}" || abort "hsPkgs doesn't have ''${hsName}";
      assert import "''${check}"    || abort "Couldn't build ''${hsName}";
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

# Turn QuickSpec output into a consistent, machine-readable format
extractEquations = writeScript "extract-eqs.sh" ''
  PAT="^[ ]*[0-9][0-9]*: "
  grep "$PAT" | sed -e "s/$PAT//g"
'';

mkQuickSpecSig = writeScript "mk-quickspec-sig" ''
  [[ -z "$SIG" ]] || return 0

  source ${getAsts}
  ${ensureVars ["DIR" "OUT_DIR" "ANNOTATED"]}

  SIG="$DIR"
  export SIG
  mkdir -p "$SIG"
  pushd "$SIG" > /dev/null

  HASKELL_NAME=$(cat "$OUT_DIR"/*.cabal | grep -i "name[ ]*:" |
                                          grep -o ":.*"       |
                                          grep -o "[^: ]*")
  NIX_EVAL_HASKELL_PKGS="${customHs}"

  export HASKELL_NAME
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
    bench --template json --output "$TIME_JSON" "$RH" 1>&2
  ''}

  WRAP="export NIX_EVAL_HASKELL_PKGS='$NIX_EVAL_HASKELL_PKGS'
  export OUT_DIR='$OUT_DIR'
  export HASKELL_NAME='$HASKELL_NAME'
  nix-shell --show-trace -p '(import $E)' --run"

  ${fileInStore "BENCH_COMMAND" ''
     $WRAP "$B"
  ''}

  ${fileInStore "RUN_COMMAND" ''
     $WRAP "$RH"
  ''}

  popd > /dev/null
'';

mkDir = writeScript "mkDir.sh" ''
  [[ -z "$DIR" ]] || return 0

  OUR_DIR=$(mktemp -d --tmpdir "quickspecBenchXXXXX")
  DIR="$OUR_DIR"
'';

mkSmt = writeScript "mkSmt.sh" ''
  [[ -z "$SMT_FILE" ]] || return 0

  source ${mkDir}
  ${ensureVars ["DIR"]}

  if [ -t 0 ]
  then
    echo "WARNING: quickspecBench needs smtlib data. You can set the
  SMT_FILE environment variable, or pipe data into stdin. Reading data
  from stdin, but it looks like a terminal; either type in your data manually
  (Ctrl-d to exit), or start again using a file or pipe." 1>&2
  fi

  SMT_FILE="$DIR/input.smt2"
  export SMT_FILE
  cat > "$SMT_FILE"
'';

mkPkgInner = ''
  ${ensureVars ["DIR"]}

  OUT_DIR="$DIR/hsPkg"
  export OUT_DIR

  mkdir -p "$OUT_DIR"
  pushd "${tipBenchmarks.te-benchmark}/lib" > /dev/null
  ./full_haskell_package.sh
  popd > /dev/null

  OUT_DIR=$(nix-store --add "$OUT_DIR")
'';

mkPkg = writeScript "mkPkg.sh" ''
  [[ -z "$OUT_DIR" ]] || return 0

  source ${mkSmt}
  ${mkPkgInner}
'';

# Use ./.. so all of our dependencies are included
getAsts = writeScript "getAsts.sh" ''
  [[ -z "$ANNOTATED" ]] || return 0

  source ${mkPkg}
  ${ensureVars ["DIR" "OUT_DIR"]}

  ANNOTATED="$DIR/annotated.json"
  STORED=$(nix-store --add "$OUT_DIR")
    EXPR="with import ${./..}/nix-support {}; annotated \"$STORED\""
       F=$(nix-build --show-trace -E "$EXPR")
  "${jq}/bin/jq" 'map(select(.quickspecable))' < "$F" > "$ANNOTATED"
'';

runSig = writeScript "runSig.sh" ''
  [[ -z "$RESULT" ]] || return 0

  source ${mkQuickSpecSig}
  ${ensureVars ["DIR" "BENCH_COMMAND" "RUN_COMMAND"]}

  RESULT="$DIR/eqs"
  "$RUN_COMMAND" | grep -v '^Depth' | "${jq}/bin/jq" -s '.' > "$RESULT"

  "$BENCH_COMMAND"
'';

mkJson = writeScript "mkJson.sh" ''
  [[ -z "$JSON_OUT" ]] || return 0

  source ${runSig}
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

  source ${mkJson}

  cat "$JSON_OUT"
'';

}
