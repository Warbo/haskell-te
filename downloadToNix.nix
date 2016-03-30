{ runScript, cabal-install, nix }:
pkgName:

# Try to download the given package from Hackage and add it to the Nix store.
# Since this derivation has a bunch of dependencies, it may be prone to
# rebuilding over and over, even when the Haskell source hasn't changed.

# To minimise the impact of this rebuilding, we use 'nix-store --add' to put the
# source into the store, rather than using e.g. 'cp foo "$out"', so that our own
# dependencies don't propagate to those who use this source.

runScript {
    inherit pkgName;
    buildInputs = [ cabal-install nix ];

    # Required for invoking Nix recursively
    NIX_REMOTE = "daemon";
    NIX_PATH   = builtins.getEnv "NIX_PATH";
  }
  ''
    DELETEME=$(mktemp -d --tmpdir "download-to-nix-XXXXX")
    cd "$DELETEME"

    export HOME="$TMPDIR"
    cabal update
    cabal get "$pkgName" || exit 1
    for D in ./*
    # */
    do
      DIR=$(nix-store --add "$D")
      printf '%s' "$DIR" > "$out"
      break
    done
  ''
