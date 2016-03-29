{ stdenv, annotatedb, jq }:
asts:

let hash = builtins.hashString "sha256" asts;
in stdenv.mkDerivation {
  inherit asts;
  name        = "download-to-nix-${hash}";
  buildInputs = [ annotatedb jq ];

  # Required for calling nix-shell during build
  NIX_REMOTE = "daemon";
  NIX_PATH   = builtins.getEnv "NIX_PATH";

  # Download pkgName to the store
  builder = builtins.toFile "run-types-builder" ''
    source "$stdenv/setup"

    mkdir -p "$out"
    runTypes < "$asts" > "$out/typed.json"
  '';
}
