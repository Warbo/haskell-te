defs: with defs;
with builtins;
with lib;

drvFromScript {} ''
  RESULT=$(nix-instantiate --eval -E '<nixpkgs>')
  if echo "$RESULT" | grep "nix-support" > /dev/null
  then
    touch "$out"
  fi
''
