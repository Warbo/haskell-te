{ stdenv, haskellPackages, nix, jq, cabal2db, lib, runCommand, writeScript }:

rec {
  runScript = env: text: with builtins; with lib;
    let hash   = unsafeDiscardStringContext (hashString "sha256" text);
        script = writeScript "script-${hash}" text;
        runner = runCommand  "runner-${hash}" env script;
    in unsafeDiscardStringContext (readFile "${runner}");

  downloadToNix   = import ./downloadToNix.nix   {
                      inherit runScript nix;
                      inherit (haskellPackages) cabal-install; };

  dumpToNix       = import ./dumpToNix.nix       {
                      inherit runScript cabal2db;              };

  downloadAndDump = import ./downloadAndDump.nix {
                      inherit dumpToNix downloadToNix;         };
}
