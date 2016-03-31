{ stdenv, annotatedb, jq }:
asts: pkgName:

let hash = builtins.hashString "sha256" asts;
in stdenv.mkDerivation {
  inherit asts pkgName;
  name        = "annotated-asts-${hash}";
  buildInputs = [ annotatedb ];

  # Required for calling nix-shell during build
  NIX_REMOTE = "daemon";
  NIX_PATH   = builtins.getEnv "NIX_PATH";

  # Download pkgName to the store
  builder = builtins.toFile "annotate-asts-builder" ''
    source "$stdenv/setup"

    mkdir -p "$out"
    annotateDb "$pkgName" < "$asts" > "$out/annotated.json" || exit 1
  '';
}
