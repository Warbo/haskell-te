{ fetchFromGitHub, path, stable }:

with rec {
  inherit (import path { inherit config; }) latestGit;

  config    = import "${stableSrc}/stable.nix";
  stableSrc = fetchFromGitHub {
    rev    = "aeab724";
    owner  = "Warbo";
    repo   = "nix-config";
    sha256 = "0jfiizlr8h5nnr3ghx5c9ij2n86vf2qqdawb0701dznabz3d2a50";
  };
  unstableSrc = latestGit {
    url    = http://chriswarbo.net/git/nix-config.git;
    stable = { unsafeSkip = true; };
  };
};

{
  nix-config-src = if stable then stableSrc else unstableSrc;
  nix-config     = if stable
                      then config
                      else import "${unstableSrc}/unstable.nix";
}
