{ glibcLocales, jq, lib, tipBenchmarks, writeScript }:

with builtins; with lib;

rec {

# We provide a fine-grained interface of env vars to allow overriding each
# stage. We define these names in Nix, e.g. { DIR = "DIR"; ... } so that
# evaluation will fail if there's a mismatch.
names = listToAttrs (map (name: { inherit name; value = name; }) [
          "DIR" "SMT_FILE" "OUT_DIR" "ANNOTATED" "SIG" "RESULT"
        ]);
vars  = mapAttrs (_: x: "$" + x) names;

# Use ./.. so all of our dependencies are included
getAnnotated = writeScript "get-annotated" ''
  STORED=$(nix-store --add "${vars.OUT_DIR}")
    EXPR="with import ${./..}/nix-support {}; annotated \"$STORED\""
  F=$(nix-build --show-trace -E "$EXPR")
  "${jq}/bin/jq" 'map(select(.quickspecable))' < "$F"
'';

mkSigHs = writeScript "mkSig.hs" ''
  {-# LANGUAGE OverloadedStrings #-}
  import MLSpec.Theory
  import Language.Eval.Internal

  cmdFor = unwords . ("runhaskell":) . flagsOf

  main = do
    [t]    <- getProjects <$> getContents
    (f, x) <- renderTheory t
    let y = withPkgs ["bench"] x
    putStrLn (cmdFor  y)
    putStrLn (pkgOf   y)
    putStrLn (buildInput f y)
'';

customHs = writeScript "custom-hs.nix" ''
  with import ${./..}/nix-support {};
  with builtins;
  let hsName = getEnv "HASKELL_NAME";
      hsDir  = getEnv "OUT_DIR";
      hsPkgs = haskellPackages.override {
        overrides = self: super:
          hsOverride self super // listToAttrs [{
            name  = hsName;
            value = self.callPackage hsDir {};
          }];
      };
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

mkQuickSpecSig = writeScript "mk-quickspec-sig" ''
  [[ -n "$OUT_DIR" ]] || {
    echo "Got no OUT_DIR" 1>&2
    exit 1
  }

  [[ -n "${vars.SIG}" ]] || {
    echo "Got no SIG" 1>&2
    exit 1
  }

  mkdir -p "${vars.SIG}"
  cd "${vars.SIG}"

  HASKELL_NAME=$(cat "$OUT_DIR"/*.cabal | grep -i "name[ ]*:" |
                                          grep -o ":.*"       |
                                          grep -o "[^: ]*")
  NIX_EVAL_HASKELL_PKGS="${customHs}"

  export HASKELL_NAME
  export NIX_EVAL_HASKELL_PKGS

  OUTPUT=$(nix-shell \
    -p '(haskellPackages.ghcWithPackages (h: [ h.mlspec h.nix-eval ]))' \
    --show-trace --run 'runhaskell ${mkSigHs}' < "${vars.ANNOTATED}")

  echo "$OUTPUT" | head -n2 | tail -n1 > env.nix
  E=$(nix-store --add env.nix)

  echo "$OUTPUT" | tail -n +3 > sig.hs
  HS=$(nix-store --add sig.hs)

  echo "export LANG='en_US.UTF-8'"                                       >  runhaskell.sh
  echo "export LOCALE_ARCHIVE=${glibcLocales}/lib/locale/locale-archive" >> runhaskell.sh
  echo "$OUTPUT" | head -n1 | tr -d '\n'                                 >> runhaskell.sh
  echo " < $HS"                                                          >> runhaskell.sh
  chmod +x runhaskell.sh
  RH=$(nix-store --add runhaskell.sh)

  echo "${benchCmd} $RH" > bench.sh
  chmod +x bench.sh
  B=$(nix-store --add bench.sh)

  cat << EOF > run.sh
  export NIX_EVAL_HASKELL_PKGS='$NIX_EVAL_HASKELL_PKGS'
  export OUT_DIR='$OUT_DIR'
  export HASKELL_NAME='$HASKELL_NAME'
  nix-shell --show-trace -p '(import $E)' --run "$B" < "$HS"
  EOF

  chmod +x run.sh
  nix-store --add run.sh

  echo "$RH"
'';

benchCmd = ''
  export LANG='en_US.UTF-8'
  export LOCALE_ARCHIVE=${glibcLocales}/lib/locale/locale-archive
  bench'';

runQuickSpecSig = writeScript "run-quickspec-sig" ''
  exit 1
'';

mkSmt = ''
  if [[ -z "${vars.SMT_FILE}" ]]
  then
    echo "Making smtlib file from stdin" 1>&2
    if [ -t 0 ]
    then
      echo "WARNING: quickspecBench needs smtlib data. You can set the
  ${names.SMT_FILE} environment variable, or pipe data into stdin. Reading data
  from stdin, but it looks like a terminal; either type in your data manually
  (Ctrl-d to exit), or start again using a file or pipe." 1>&2
    fi

    ${names.SMT_FILE}="${vars.DIR}/input.smt2"
    export ${names.SMT_FILE}
    cat > "${ vars.SMT_FILE}"
  fi
'';

mkPkg = ''
  if [[ -z "${vars.OUT_DIR}" ]]
  then
    echo "Generating Haskell package" 1>&2
    ${names.OUT_DIR}="${vars.DIR}/hsPkg"
    export ${names.OUT_DIR}
    mkdir -p "${vars.OUT_DIR}"
    pushd "${tipBenchmarks.te-benchmark}/lib" > /dev/null
    ./full_haskell_package.sh
    popd > /dev/null
  fi
'';

getAsts = ''
  if [[ -z "${vars.ANNOTATED}" ]]
  then
    echo "Getting ASTs from Haskell" 1>&2
    ${names.ANNOTATED}="${vars.DIR}/annotated.json"
    "${getAnnotated}" > "${vars.ANNOTATED}"
  fi
'';

mkSig = ''
  if [[ -z "${vars.SIG}" ]]
  then
    echo "Making signature for QuickSpec" 1>&2
    ${names.SIG}="${vars.DIR}/sig.hs"
    export ${names.SIG}
    "${mkQuickSpecSig}"
  fi
'';

runSig = ''
  if [[ -z "${vars.RESULT}" ]]
  then
    echo "Running QuickSpec" 1>&2
    ${names.RESULT}="${vars.DIR}/result"
    "${runQuickSpecSig}" > "${vars.RESULT}"
  fi
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

  if [[ -z "${vars.DIR}" ]]
  then
    echo "Making temp dir" 1>&2
    OUR_DIR=$(mktemp -d --tmpdir "quickspecBenchXXXXX")
    ${names.DIR}="$OUR_DIR"
  fi

  ${mkSmt}

  ${mkPkg}

  ${getAsts}

  ${mkSig}

  ${runSig}

  cat "${vars.RESULT}"
'';

}
