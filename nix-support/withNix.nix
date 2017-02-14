{ bash, coreutils, jq, lib, nix, nixEnv, perl, procps, runCommand, utillinux }:
with builtins;
with nixEnv;
with rec {
  commonDeps = [ bash coreutils jq nix perl procps utillinux ];
};

env:
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
        buildInputs = existing ++ commonDeps;

        # Required for calling nix recursively
        NIX_PATH   = lib.concatStringsSep ":" parts;
        NIX_REMOTE = nixRemote;
      }
