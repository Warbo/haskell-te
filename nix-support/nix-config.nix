{ fetchFromGitHub, path }:

with rec {
  nix-config = import "${configSrc}";

  configSrc = with builtins.tryEval <nix-config>;
              if success then value else stableSrc;

  stableSrc = fetchFromGitHub {
    owner  = "Warbo";
    repo   = "nix-config";
    rev    = "796865f";
    sha256 = "132v4w8a1lf99d8n7w743cq7rdqj5w56a10f9xa9vmqx2lazhzvx";
  };
};

{ inherit nix-config; }
