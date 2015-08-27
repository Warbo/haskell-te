# FIXME: Quick hack until QuickCheck bug #63 is fixed
with import <nixpkgs> {};
stdenv.lib.overrideDerivation haskellPackages.QuickCheck (old: {
  src = fetchFromGitHub {
    owner  = "warbo";
    repo   = "quickcheck";
    rev    = "e9f8708ba1";
    sha256 = "01gaixgz6jr0xz6xc3mwm5scsjymrg2yi5z9gcr18bj5dnqm468z";
  };
});
