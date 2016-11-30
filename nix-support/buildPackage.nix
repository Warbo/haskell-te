{ runCmd, cabal2nix, cabal-install, drvFromScript, explore, stdParts,
  storeParts, writeScript }:

{ src, hsEnv }:

drvFromScript { buildInputs = explore.extractedEnv {
                  extraPkgs = [ cabal2nix cabal-install ];
                };
                outputs = stdParts;
              } ''
  set -e
  cp -r "${src}" ./src
  chmod +w -R ./src
  cd ./src

  export HOME="$TMPDIR"
  nix-shell --pure --show-trace -E "$(cabal2nix --shell ./.)" \
                   --run '"${cabal-install}/bin/cabal" configure' || {
    echo '{"failed":true}' > "$out"
    exit 0
  }

  O=$("${runCmd {
           cmd  = "cabal";
           args = ["build"];
       }}")

  ${storeParts}
''
