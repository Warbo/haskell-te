{ stdenv, adb-scripts, jq }:
asts: pkgName:

let hash = builtins.hashString "sha256" asts;
in stdenv.mkDerivation {
  inherit asts pkgName;
  name        = "typed-asts-${hash}";
  buildInputs = [ adb-scripts jq ];

  # Required for calling nix-shell during build
  NIX_REMOTE = "daemon";
  NIX_PATH   = builtins.getEnv "NIX_PATH";

  # Download pkgName to the store
  builder = builtins.toFile "run-types-builder" ''
    source "$stdenv/setup"

    runTypes "$pkgName" < "$asts" > typed.json || exit 1

    RESULT=$(nix-store --add typed.json)
    printf '%s' "$RESULT" > "$out"
  '';
}
