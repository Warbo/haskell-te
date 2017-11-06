{ fetchFromGitHub, path, stable }:

with rec {
  inherit (import path { inherit config; }) latestGit;

  config    = import "${stableSrc}/stable.nix";
  stableSrc = fetchFromGitHub {
    rev    = "d04e76b";
    owner  = "Warbo";
    repo   = "nix-config";
    sha256 = "18bzr5xcch8naswxcznxz36f28ab4266yfs0v5b9xmdy65ysgjln";
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
