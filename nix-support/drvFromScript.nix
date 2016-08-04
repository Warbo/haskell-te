{ bash, explore, haskellPackages, lib, nix, perl, procps, runCommand, writeScript }:
with builtins;

let # Required for running 'timeout'
    timeoutDeps = [ perl procps bash ];

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
            # Required for calling nix recursively
            buildInputs = existing    ++
                          timeoutDeps ++
                          [ nix ]     ++
                          (if any (e: lib.hasPrefix "ghc-" e.name) existing
                              then []
                              else trace "Warning: No GHC in environment" []);

            NIX_PATH    = lib.concatStringsSep ":" parts;

            # Allows ~/.nixpkgs/config.nix to help debugging
            USER_HOME   = getEnv "HOME";

            NIX_REMOTE  =
              let given  = getEnv "NIX_REMOTE";
                  force  = readFile result;
                  result = runCommand "get-nix-remote"
                             { buildInputs = [ nix ]; }
                             ''
                               if nix-instantiate \
                                    --eval \
                                    -E null 2> /dev/null
                               then
                                 printf "$NIX_REMOTE" > "$out"
                               else
                                 printf "daemon"      > "$out"
                               fi
                             '';
               in if given == ""  # Nix is writable, or we
                     then force   # need to force 'daemon'.
                     else given;  # Propagate the given value
          };

in env: text:
     let script = writeScript "script" text;
      in runCommand  "runner" (withNix env) script
