{ nix, runCommand }:

with builtins;
{
  # Ensure we can write to the Nix store (or ask a builders to do so for us)
  nixRemote  =
    let given  = getEnv "NIX_REMOTE";
        force  = import result;
        result = runCommand "nix-remote.nix" { buildInputs = [ nix ]; } ''
          if nix-instantiate --eval -E null 2> /dev/null
          then
            printf "\"$NIX_REMOTE\"" > "$out"
          else
            printf '"daemon"'        > "$out"
          fi
        '';
     in if given == ""
           then force   # Nix is writable, or we need to force 'daemon'
           else given;  # Propagate the existing value
}
