{ callPackage, fetchFromGitHub }:

with {
  src = fetchFromGitHub {
    owner  = "Warbo";
    repo   = "asv-nix";
    rev    = "433f0fa";
    sha256 = "1zb3l1h2zdixs4x6cihvjimw3gyfns5n78acm6ylac3hdn55lpq2";
  };
};
import "${src}"
