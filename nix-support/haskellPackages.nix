{ callHackage, extractTarball, fetchFromGitHub, fetchgit, fetchurl, haskell,
  lib, nix-config, nixFromCabal, stable, superHaskellPackages }:

with builtins;
with lib;

with rec {
  # Get particular Hackage revisions, when those in haskellPackages don't work
  overrides = callPackage: mapAttrs (n: v: callPackage (callHackage n v) {}) {
    haskell-src-exts = "1.19.0";
    pretty-show      = "1.6.12";
    tasty            = "0.11.2.1";
  };

  # Get packages from git repos
  hsPkgs = { get }: {
    AstPlugin = get {
      path   = <ast-plugin>;
      url    = https://github.com/Warbo/ast-plugin.git;
      rev    = "a04f6fe";
      sha256 = "1gmkv4l38vpvhg2h8dwv4gf8dq1d0lr0zxd5j9szi90xb8nl2241";
    } {};

    bench  = get {
      url    = https://github.com/Gabriel439/bench.git;
      rev    = "2575ff3";
      sha256 = "18xplqhhqn9y7byib01sv75i4wbgg73rz53bn1ppd5mfxhdp8g8x";
    } {};

    GetDeps = get {
      path   = <get-deps>;
      url    = https://github.com/Warbo/getDeps.git;
      rev    = "7c02fbc";
      sha256 = "0iw9ajzmq439qipm5r21dby32xlmdxg8bnsm6bcgm8dr9whhalfl";
    } {};

    HS2AST = get {
      path   = <hs2ast>;
      url    = https://github.com/Warbo/hs2ast.git;
      rev    = "469d999";
      sha256 = "1yancv9pd8rnkpla462czsi4kgd8nvndjixmr1s6kkc7xk68zky8";
    } {};

    ifcxt = get {
      path   = <ifcxt>;
      url    = https://github.com/mikeizbicki/ifcxt.git;
      rev    = "7f9f876";
      sha256 = "1k267zs3w999xg90ddy02l4cpjn14x07cdgqbca3w0ncili2p7a2";
    } {};

    ML4HSFE = get {
      path   = <ml4hsfe>;
      url    = https://github.com/Warbo/ml4hsfe.git;
      rev    = "bcdd93b";
      sha256 = "0rraj7ias334g39vyc5z9afms4w30g5vf1czgw7fskahiir2vmi1";
    } {};

    mlspec = get {
      path   = <mlspec>;
      url    = https://github.com/Warbo/mlspec.git;
      rev    = "a5f0dd2";
      sha256 = "1m2vs51wqdqlv67z1qcv3jhwapb9dp5k336vjvjkqpr8svg15yas";
    } {};

    mlspec-helper = get {
      path   = <mlspec-helper>;
      url    = https://github.com/Warbo/mlspec-helper.git;
      rev    = "1bf9c32";
      sha256 = "119kb41gv9v2fs1wgvjpr4skz5bbmp2apgllmxbxw4zw3xww1rlr";
    } {};

    nix-eval = get {
      path   = <nix-eval>;
      url    = https://github.com/Warbo/nix-eval.git;
      rev    = "53d18a2";
      sha256 = "1agw1zppbhgk6aaqd75mmvbd6r8d67ap4y5rli1sm1j1q0a5qqx5";
    } {};

    reduce-equations = get {
      path   = <reduce-equations>;
      url    = https://github.com/Warbo/reduce-equations.git;
      rev    = "a86199b";
      sha256 = "11dafq0zl6vj1lzybsfpryvc2rqbxxkjjy3v4ab1vb8nzhxfgna3";
    } {};

    runtime-arbitrary = get {
      path   = <runtime-arbitrary>;
      url    = https://github.com/Warbo/runtime-arbitrary;
      rev    = "5b7ff2f";
      sha256 = "11gnfmz48vxvf42xs9255r51vbv1sjghvzi60gcrpx3jk38d2gyb";
    } {};

    spoon = get {
      url    = https://github.com/Warbo/spoon.git;
      rev    = "4424f9a";
      sha256 = "1d14qawzf7pimkjccj3f2vy9nc4fb2w00ib8li4kb180fb6wjvq4";
    } {};

    weigh = get {
      url    = https://github.com/fpco/weigh.git;
      rev    = "26f8e3e";
      sha256 = "0pmkzlcjfqi41qmrgjyw1y7naclq86kb6mp0i4ni3d1lkiylb9gc";
    } {};
  };
};

assert let ghcVersion = superHaskellPackages.ghc.version;
           reqVersion = "7.10.3";
        in ghcVersion == reqVersion ||
           abort "Using GHC ${ghcVersion} (should be ${reqVersion})";
rec {
  hsOverride = self: super: overrides self.callPackage // hsPkgs {
    get = { path ? null, url, rev, sha256}:
          with rec {
            git = nix-config.latestGit {
              inherit url;
              stable = { inherit rev sha256; };
            };
            src = with tryEval path;
                  if success && value != null
                     then value
                     else git;
          };
          self.callPackage (nixFromCabal (toString src) null);
  };

  haskellPackages = superHaskellPackages.override { overrides = hsOverride; };
}
