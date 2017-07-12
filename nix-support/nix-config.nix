{ fetchFromGitHub }:

with {
  src = fetchFromGitHub {
    owner  = "Warbo";
    repo   = "nix-config";
    rev    = "4f1ce04";
    sha256 = "07vginvg9nm3ghny7f80j2pdkgv3bddf28v1mskd57d4rqjcc2zc";
  };
};
import <nixpkgs> { config = import "${src}/config.nix"; }
