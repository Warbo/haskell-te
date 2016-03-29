{ stdenv, annotatedb, jq }:
asts: pkgName:

let hash = builtins.hashString "sha256" asts;
in stdenv.mkDerivation {
  inherit asts pkgName;
  name        = "typed-asts-${hash}";
  buildInputs = [ annotatedb jq ];

  # Required for calling nix-shell during build
  NIX_REMOTE = "daemon";
  NIX_PATH   = builtins.getEnv "NIX_PATH";

  # Download pkgName to the store
  builder = builtins.toFile "run-types-builder" ''
    source "$stdenv/setup"

    mkdir -p "$out"
    runTypes "$pkgName" < "$asts" > "$out/typed.json" || exit 1
  '';
}
