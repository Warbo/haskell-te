{ stdenv, haskellPackages, nix, jq, cabal2db, lib }:

rec {
  downloadToNix   = import ./downloadToNix.nix   { inherit stdenv haskellPackages nix;    };
  dumpToNix       = import ./dumpToNix.nix       { inherit stdenv cabal2db lib;           };
  build           = import ./build.nix           { inherit stdenv haskellPackages;        };
  downloadAndDump = import ./downloadAndDump.nix { inherit dumpToNix downloadToNix;       };
}
