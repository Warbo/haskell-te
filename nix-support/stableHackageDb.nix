{ fetchFromGitHub, tePath }:

with rec {
  # stableHackageDb was removed from later helpers
  src = fetchFromGitHub {
    owner  = "Warbo";
    repo   = "nix-helpers";
    rev    = "35797e2";
    sha256 = "0mj1q72sjbdalcvaqk3pk1ik9k1bgqmd5igv20ks2miwg5hr2bic";
  };

  helpers = import tePath { overlays = [ (import "${src}/overlay.nix") ]; };
};
helpers.stableHackageDb.overrideAttrs (old: {
  # Try to bypass the Nix sandbox, if it's enabled
  __noChroot = true;
})
