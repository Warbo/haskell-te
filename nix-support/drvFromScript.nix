{ bash, explore, haskellPackages, jq, lib, nix, perl, procps, runCommand,
  utillinux, writeScript }:
with builtins;

let commonDeps = [ bash jq nix perl procps utillinux ];

    # Ensure we can write to the Nix store (or ask a builders to do so for us)
    nixRemote  =
      let given  = getEnv "NIX_REMOTE";
          force  = readFile result;
          result = runCommand "get-nix-remote" { buildInputs = [ nix ]; } ''
            if nix-instantiate --eval -E null 2> /dev/null
            then
              printf "$NIX_REMOTE" > "$out"
            else
              printf "daemon"      > "$out"
            fi
          '';
       in if given == ""
             then force   # Nix is writable, or we need to force 'daemon'
             else given;  # Propagate the existing value

    withNix = env:
      let existing = if env ? buildInputs
                        then env.buildInputs
                        else [];
          # If we don't have <real> yet, use <nixpkgs>
          real     = toString
                       (if any (p: p.prefix == "real")
                               nixPath
                           then <real>
                           else <nixpkgs>);
          # Override <nixpkgs>, with <real> as a fallback
          parts    = [ "nixpkgs=${toString ./.}"
                       "real=${real}"
                       (getEnv "NIX_PATH") ];
       in env // {
            # Haskell packages are tricky, as they must be accumulated in the
            # return value of the callback given to 'ghcWithPackages'. Getting
            # this wrong is common enough to make a "No GHC" warning helpful!
            buildInputs =  (if any (e: lib.hasPrefix "ghc-" e.name) existing
                               then (x: x)
                               else trace "Warning: No GHC in environment")
                             (existing ++ commonDeps);

            # Required for calling nix recursively
            NIX_PATH   = lib.concatStringsSep ":" parts;
            NIX_REMOTE = nixRemote;
          };

in env: text:
     let script = writeScript "script" text;
      in runCommand  "runner" (withNix env) script
