{ callPackage, fetchgit }:

with {
  src = fetchgit {
    url    = http://chriswarbo.net/git/render-eqs.git;
    rev    = "2d1ff3f";
    sha256 = "1a16g359kg1gyai1dg6jif72nbrvzpwn04kz6ywkx69rikzsd5wf";
  };
};
callPackage "${src}" {}
