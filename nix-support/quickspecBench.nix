{ glibcLocales, jq, lib, tipBenchmarks, writeScript }:

# Provide a script which accepts smtlib data, runs it through QuickSpec and
# outputs the resulting equations along with benchmark times. The script should
# be runnable from the commandline, as long as the haskell-te package is in PATH

with builtins; with lib;

rec {

# We provide a fine-grained interface of env vars to allow overriding each
# stage. We define these names in Nix, e.g. { DIR = "DIR"; ... } so that
# evaluation will fail if there's a mismatch.
names = listToAttrs (map (name: { inherit name; value = name; }) [
          "DIR" "SMT_FILE" "OUT_DIR" "ANNOTATED" "SIG" "RESULT" "BENCH_COMMAND"
        ]);
vars  = mapAttrs (_: x: "$" + x) names;

mkSigHs = writeScript "mkSig.hs" ''
  {-# LANGUAGE OverloadedStrings #-}
  import MLSpec.Theory
  import Language.Eval.Internal

  -- Reads JSON from stdin, outputs a QuickSpec signature and associated shell
  -- and Nix commands for running it
  main = do
    [t]    <- getProjects <$> getContents
    (f, x) <- renderTheory t
    let y = withPkgs ["bench"] x
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
            value = self.callPackage (nixedHsPkg hsDir null) {};
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

mkQuickSpecSig = writeScript "mk-quickspec-sig" ''
  [[ -z "${vars.SIG}" ]] || return 0

  source ${getAsts}

  ${names.SIG}="${vars.DIR}"
  export ${names.SIG}
  mkdir -p "${vars.SIG}"
  pushd "${vars.SIG}" > /dev/null

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
  ${names.BENCH_COMMAND}=$(nix-store --add run.sh)
  popd > /dev/null
'';

benchCmd = ''
  export LANG='en_US.UTF-8'
  export LOCALE_ARCHIVE=${glibcLocales}/lib/locale/locale-archive
  bench'';

mkDir = writeScript "mkDir.sh" ''
  [[ -z "${vars.DIR}" ]] || return 0

  OUR_DIR=$(mktemp -d --tmpdir "quickspecBenchXXXXX")
  ${names.DIR}="$OUR_DIR"
'';

mkSmt = writeScript "mkSmt.sh" ''
  [[ -z "${vars.SMT_FILE }" ]] || return 0

  source ${mkDir}

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
'';

mkPkg = writeScript "mkPkg.sh" ''
  [[ -z "${vars.OUT_DIR}" ]] || return 0

  source ${mkSmt}

  ${names.OUT_DIR}="${vars.DIR}/hsPkg"
  export ${names.OUT_DIR}

  mkdir -p "${vars.OUT_DIR}"
  pushd "${tipBenchmarks.te-benchmark}/lib" > /dev/null
  ./full_haskell_package.sh
  popd > /dev/null
'';

# Use ./.. so all of our dependencies are included
getAsts = writeScript "getAsts.sh" ''
  [[ -z "${vars.ANNOTATED}" ]] || return 0

  source ${mkPkg}

  ${names.ANNOTATED}="${vars.DIR}/annotated.json"
  STORED=$(nix-store --add "${vars.OUT_DIR}")
    EXPR="with import ${./..}/nix-support {}; annotated \"$STORED\""
       F=$(nix-build --show-trace -E "$EXPR")
  "${jq}/bin/jq" 'map(select(.quickspecable))' < "$F" > "${vars.ANNOTATED}"
'';

runSig = writeScript "runSig.sh" ''
  [[ -z "${vars.RESULT}" ]] || return 0

  source ${mkQuickSpecSig}

  ${names.RESULT}="${vars.DIR}/result"
  "${vars.BENCH_COMMAND}" > "${vars.RESULT}"
'';

script = writeScript "quickspec-bench" ''
  #!/usr/bin/env bash
  set -ex

  function cleanup {
    if [[ -n "$OUR_DIR" ]] && [[ -d "$OUR_DIR" ]]
    then
      rm -rf "$OUR_DIR"
    fi
  }
  trap cleanup EXIT

  source ${runSig}
  cat "${vars.RESULT}"
'';

}
