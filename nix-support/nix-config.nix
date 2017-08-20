{ fetchFromGitHub, fetchgit }:

with builtins;
with rec {
  gh = fetchFromGitHub {
    inherit rev;
    owner  = "Warbo";
    repo   = "nix-config";
    sha256 = "09ywhxh4jx51ndblnhxmn5qr701icy1r599y22l3jfkzbb8jcs6p";
  };

  local = fetchgit {
    inherit rev;
    url    = "${getEnv "GIT_REPO_DIR"}/nix-config.git";
    sha256 = "0k7i4m7x395p9i1gad4xw6mb68d1winysw03pb269nxjwr6xzxlh";
  };

  rev    = "5c11ef6";
  chosen = if getEnv "GIT_REPO_DIR" == ""
              then gh
              else local;

  path = with tryEval <real>;
         if success then value else <nixpkgs>;
};
{
  nix-config-src = chosen;
  nix-config     = import path { config = import "${chosen}/config.nix"; };
}
