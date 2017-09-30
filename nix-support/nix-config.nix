{ fetchFromGitHub, stable }:

with rec {
  stableSrc = fetchFromGitHub {
    rev    = "76d441a";
    owner  = "Warbo";
    repo   = "nix-config";
    sha256 = "047vqfyb7qbl49hyi93vfz5dkqpz89jjscs1w5kc29hn6881v0w8";
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
