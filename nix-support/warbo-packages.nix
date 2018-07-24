{ fetchFromGitHub, lib, path }:

with {
  defs = import ./addOverlayToNixpkgs.nix {
    inherit lib path;
    src = fetchFromGitHub {
      owner  = "Warbo";
      repo   = "warbo-packages";
      rev    = "21c07e0";
      sha256 = "19y7h658s013ikqmj4dsnfyx9962q3ybbvzi2bczzcg3zhplqmd3";
    };
  };
};
defs.warbo-packages
