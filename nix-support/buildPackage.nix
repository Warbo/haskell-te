{ benchmark, cabal2nix, cabal-install, parseJSON, runScript, withNix }:

{ src, quick, hsEnv }:

parseJSON (runScript { buildInputs = [ cabal2nix cabal-install ]; } ''
  set -e
  cp -r "${src}" ./src
  chmod +w -R ./src
  cd ./src
  echo "NIX_PATH: $NIX_PATH" 1>&2
  export HOME="$TMPDIR"
  nix-shell --pure --show-trace -E "$(cabal2nix --shell ./.)" \
                   --run '"${cabal-install}/bin/cabal" configure'

  "${benchmark quick "cabal" ["build"]}" > "$out"
'')
