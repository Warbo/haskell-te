{ stdenv, haskellPackages, nix, gnutar, jq, lib, runCommand, writeScript,
  doCheck ? true }:

rec {
  c2db-scripts    = import ./scripts.nix         {
                      inherit stdenv nix jq doCheck;
                      inherit (haskellPackages) cabal-install;
                    };

  runScript       = import ./runScript.nix       {
                      inherit lib writeScript runCommand;
                    };

  importDir       = import ./importDir.nix       {
                      inherit lib;
                    };

  withNix         = env: let existing = if env ? buildInputs
                                           then env.buildInputs
                                           else [];
                          in env // {
                               # Required for calling nix recursively
                               buildInputs = existing ++ [ nix ];
                               NIX_REMOTE  = "daemon";
                               NIX_PATH    = builtins.getEnv "NIX_PATH";
                               # Allows ~/.nixpkgs/config.nix to help debugging
                               USER_HOME   = builtins.getEnv "HOME";
                             };
}
