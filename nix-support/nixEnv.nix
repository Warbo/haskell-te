# Env vars required for using Nix commands inside builders
{ lib, nix, runCommand }:

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
};

# Return a thunk, to prevent callPackage polluting our attrset with
# "overrideDerivation" and friends.
_: {
   NIX_PATH   = concatStringsSep ":" pathParts;

   NIX_REMOTE = if remoteGiven == ""
                   then remoteForce   # Nix is writable, or we need to force
                   else remoteGiven;  # Propagate the existing value
}
