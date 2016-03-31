{ stdenv, haskellPackages, nix, jq, lib, runCommand, writeScript, doCheck ? true }:

rec {
  scripts         = import ./scripts.nix {
                      inherit stdenv nix jq doCheck;
                      inherit (haskellPackages) cabal-install; };

  runScript       = import ./runScript.nix {
                      inherit lib writeScript runCommand;      };

  downloadToNix   = import ./downloadToNix.nix   {
                      inherit runScript nix;
                      inherit (haskellPackages) cabal-install; };

  dumpToNix       = import ./dumpToNix.nix       {
                      inherit runScript scripts;               };

  downloadAndDump = import ./downloadAndDump.nix {
                      inherit dumpToNix downloadToNix;         };

  importDir       = import ./importDir.nix {
                      inherit lib;                             };
}
