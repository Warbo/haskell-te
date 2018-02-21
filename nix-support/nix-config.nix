{ fetchFromGitHub, path, stable }:

with rec {
  inherit (import path { inherit config; }) latestGit;

  config    = import "${stableSrc}/stable.nix";
  stableSrc = fetchFromGitHub {
    rev    = "eb34052";
    owner  = "Warbo";
    repo   = "nix-config";
    sha256 = "0js6af9xi9v576lh2jma6qjhfpjw8r0grrxbh5x6hr97399jryld";
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
