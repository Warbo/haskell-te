{ fetchFromGitHub, path, stable }:

with rec {
  inherit (import path { inherit config; }) latestGit;

  config    = import "${stableSrc}/stable.nix";
  stableSrc = fetchFromGitHub {
    rev    = "5ce17f9";
    owner  = "Warbo";
    repo   = "nix-config";
    sha256 = "038biw9nqsp8swbdzw0lnkxx83ii16bp97hhjypq02vz8rn2x4zj";
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
