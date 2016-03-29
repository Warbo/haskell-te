{ stdenv, haskellPackages, nix, jq }:

rec {
  cabal2db      = import ./cabal2db.nix      { inherit stdenv haskellPackages nix jq; };
  downloadToNix = import ./downloadToNix.nix { inherit stdenv haskellPackages; };
  dumpToNix     = import ./dumpToNix.nix     { inherit stdenv cabal2db; };
  build         = import ./build.nix         { inherit stdenv haskellPackages; };
}
