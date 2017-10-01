{ fetchFromGitHub, stable }:

with rec {
  stableSrc = fetchFromGitHub {
    rev    = "c7c36d4";
    owner  = "Warbo";
    repo   = "nix-config";
    sha256 = "018gyj9i002wrj3krzrv4w0lf9606142ba5ci4wy1ams48bdszbr";
  };
  config      = import "${stableSrc}/stable.nix";
  unstableSrc = (import <nixpkgs> { inherit config; }).latestNixCfg;
};

{
  nix-config-src = if stable then stableSrc else unstableSrc;
  nix-config     = if stable
                      then config
                      else import "${unstableSrc}/unstable.nix";
}
