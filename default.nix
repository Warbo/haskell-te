{ stdenv, haskellPackages, nix, jq }:

(import ./defs.nix { inherit stdenv haskellPackages nix jq; }).cabal2db
