{ stdenv, haskellPackages, nix }:
pkgName:

# Try to download the given package from Hackage and add it to the Nix store.
# Since this derivation has a bunch of dependencies, it may be prone to
# rebuilding over and over, even when the Haskell source hasn't changed.

# To minimise the impact of this rebuilding, we use 'nix-store --add' to put the
# source into the store, rather than using e.g. 'cp foo "$out"', so that our own
# dependencies don't propagate to those who use this source.

let fresh = stdenv.mkDerivation {
  inherit pkgName;
  name        = "download-to-nix-${pkgName}";
  buildInputs = [ haskellPackages.cabal-install nix ];

  # Required for calling nix-shell during build
  NIX_REMOTE = "daemon";
  NIX_PATH   = builtins.getEnv "NIX_PATH";

  # Download pkgName to the store
  builder = builtins.toFile "download-to-nix-builder" ''
    source "$stdenv/setup"

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
  '';
};
in with builtins; unsafeDiscardStringContext (readFile "${fresh}")
