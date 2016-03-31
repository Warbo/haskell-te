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

  downloadToNix   = import ./downloadToNix.nix   {
                      inherit runScript nix;
                      inherit (haskellPackages) cabal-install;
                    };

  dumpToNix       = import ./dumpToNix.nix       {
                      inherit runScript c2db-scripts withNix;
                    };

  downloadAndDump = import ./downloadAndDump.nix {
                      inherit dumpToNix downloadToNix;
                    };

  importDir       = import ./importDir.nix       {
                      inherit lib;
                    };

  assertMsg       = cond: msg: builtins.addErrorContext msg (assert cond; cond);

  dumpedPackages  = import ./dumpedPackages.nix  {
                      inherit dumpToNix runScript gnutar haskellPackages lib
                              withNix;
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
