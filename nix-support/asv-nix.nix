{ callPackage, fetchFromGitHub, nix-config }:

with {
  src = fetchFromGitHub {
    owner  = "Warbo";
    repo   = "asv-nix";
    rev    = "d5af74d";
    sha256 = "1jp5a8p5dzh2vb2s9k2wf3j2l9fcm7l47ydqy8wlrjiyqlc4jw7a";
  };
};
callPackage "${src}" {
  inherit (nix-config) asv;
}
