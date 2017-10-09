# Env vars required for using Nix commands inside builders
{ fail, jq, lib, nix, runCommand }:

with builtins;
with lib;
with rec {

  # Override <nixpkgs>, with <real> as a fallback. Use toString so the path
  # appears as-is, rather than being added to the Nix store.
  pathParts = [ "nixpkgs=${toString ./.}"
                   "real=${toString pathReal}"
                (getEnv "NIX_PATH") ];

  # If we don't have <real> yet, use <nixpkgs>
  pathReal = with tryEval <real>;
             if success then value else <nixpkgs>;

  remoteGiven = getEnv "NIX_REMOTE";

  # Ensure we can write to the Nix store (or ask a builders to do so for us)
  remoteForce  = import remoteResult;
  remoteResult = runCommand "nix-remote.nix" { buildInputs = [ nix ]; } ''
    if nix-instantiate --eval -E null 2> /dev/null
    then
      printf "\"$NIX_REMOTE\"" > "$out"
    else
      printf '"daemon"'        > "$out"
    fi
  '';

  checkPath = runCommand "try-nix-path.nix"
    {
      inherit NIX_REMOTE;
      NIX_PATH    = concatStringsSep ":" pathParts;
      buildInputs = [ fail jq nix ];
    }
    ''
      set -e
      echo "Checking <nixpkgs> gets overridden" 1>&2
      RESULT=$(nix-instantiate --eval -E '<nixpkgs>')
      echo "$RESULT" | grep "nix-support" > /dev/null ||
        fail "Didn't see 'nix-support' in <nixpkgs> ($RESULT)"

      echo "Checking <nixpkgs> isn't polluted by ~/.nixpkgs/config.nix" 1>&2
      nix-instantiate --eval \
                      -E 'with builtins;
                          assert !((import <nixpkgs> {}) ?
                                     warbo-utilities); true'
      nix-instantiate --eval \
                      -E 'with builtins;
                          assert !((import <nixpkgs> {}).haskellPackages ?
                                     haskell-example); true'

      echo "$NIX_PATH" | jq -R '.' > "$out"
    '';

  NIX_REMOTE = if remoteGiven == ""
                  then remoteForce   # Nix is writable, or we need to force
                  else remoteGiven;  # Propagate the existing value
};

{
  value = {
    inherit NIX_REMOTE;
    NIX_PATH = import checkPath;
  };
  removeOverrides = true;  # Since they can't be serialised into an environment
}
