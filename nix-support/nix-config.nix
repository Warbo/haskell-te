{ fetchFromGitHub, path, stable }:

with rec {
  inherit (import path { inherit config; }) latestGit;

  config    = import "${stableSrc}/stable.nix";
  stableSrc = fetchFromGitHub {
    rev    = "8abcf84";
    owner  = "Warbo";
    repo   = "nix-config";
    sha256 = "0cjh7y1z8wfm542yrwnhaj81yikf05va7ahlg195jqf5vqj6m4yd";
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
