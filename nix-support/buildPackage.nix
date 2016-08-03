{ benchmark, cabal2nix, cabal-install, parseJSON, runScript, writeScript }:

{ src, quick, hsEnv }:

parseJSON (runScript { buildInputs = [ cabal2nix cabal-install ]; } ''
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

  "${benchmark quick "cabal" ["build"] []}" > "$out"
'')
