{ stdenv, annotatedb }:

asts:

stdenv.mkDerivation {
  inherit asts;
  name = "annotate-asts";
  buildInputs = [ annotatedb ];

  # Required for calling nix-shell during build
  NIX_REMOTE = "daemon";
  NIX_PATH   = builtins.getEnv "NIX_PATH";

  # Send asts through annotatedb
  builder = builtins.toFile "annotate-asts-builder" ''
    source "$stdenv/setup"

    mkdir -p "$out"
    annotatedb < "$asts" > "$out/annotated.json"
  '';
}
