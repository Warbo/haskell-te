defs: with defs;
with builtins;
with lib;

let
  nixPath = runScript {} ''
    RESULT=$(nix-instantiate --eval -E '<nixpkgs>')
    printf '%s' "$RESULT" > "$out"
  '';
in
testMsg (hasSuffix "nix-support" nixPath)
        "<nixpkgs> is '${toJSON nixPath}'"
