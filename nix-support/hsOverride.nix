{ callHackage, lib, nix-config, nixFromCabal, stable }:

with builtins;
with lib;

with rec {
  hsPkgs = { get, hackagePkg }: {
    tasty = hackagePkg "tasty" "0.11.2.1" {};

    AstPlugin = get {
      path   = <ast-plugin>;
      repo   = "ast-plugin";
      rev    = "a04f6fe";
      sha256 = "1gmkv4l38vpvhg2h8dwv4gf8dq1d0lr0zxd5j9szi90xb8nl2241";
    } {};

    bench  = get {
      owner  = "Gabriel439";
      repo   = "bench";
      rev    = "2575ff3";
      sha256 = "18xplqhhqn9y7byib01sv75i4wbgg73rz53bn1ppd5mfxhdp8g8x";
    } {};

    GetDeps = get {
      path   = <get-deps>;
      repo   = "getDeps";
      rev    = "7c02fbc";
      sha256 = "0iw9ajzmq439qipm5r21dby32xlmdxg8bnsm6bcgm8dr9whhalfl";
    } {};

    HS2AST = get {
      path   = <hs2ast>;
      repo   = "hs2ast";
      rev    = "469d999";
      sha256 = "1yancv9pd8rnkpla462czsi4kgd8nvndjixmr1s6kkc7xk68zky8";
    } {};

    ifcxt = get {
      path   = <ifcxt>;
      owner  = "mikeizbicki";
      repo   = "ifcxt";
      rev    = "7f9f876";
      sha256 = "1k267zs3w999xg90ddy02l4cpjn14x07cdgqbca3w0ncili2p7a2";
    } {};

    ML4HSFE = get {
      path   = <ml4hsfe>;
      repo   = "ml4hsfe";
      rev    = "bcdd93b";
      sha256 = "0rraj7ias334g39vyc5z9afms4w30g5vf1czgw7fskahiir2vmi1";
    } {};

    mlspec = get {
      path   = <mlspec>;
      repo   = "mlspec";
      rev    = "82c123c";
      sha256 = "0wyinmqfgy8l31lzxklm41a47678sw9jgy9jrn540n6ihc1jal8d";
    } {};

    mlspec-helper = get {
      path   = <mlspec-helper>;
      repo   = "mlspec-helper";
      rev    = "d794706";
      sha256 = "1vaniwziqq0w1ajrabxbyf76iqplk7c765z13k5kpndhmqmsga5r";
    } {};

    nix-eval = get {
      path   = <nix-eval>;
      repo   = "nix-eval";
      rev    = "53d18a2";
      sha256 = "1agw1zppbhgk6aaqd75mmvbd6r8d67ap4y5rli1sm1j1q0a5qqx5";
    } {};

    reduce-equations = get {
      path   = <reduce-equations>;
      repo   = "reduce-equations";
      rev    = "a86199b";
      sha256 = "11dafq0zl6vj1lzybsfpryvc2rqbxxkjjy3v4ab1vb8nzhxfgna3";
    } {
      haskell-src-exts = hackagePkg "haskell-src-exts" "1.19.0" {
        pretty-show = hackagePkg "pretty-show" "1.6.12" {};
      };
    };

    runtime-arbitrary = get {
      path   = <runtime-arbitrary>;
      repo   = "runtime-arbitrary";
      rev    = "5b7ff2f";
      sha256 = "06kpz8vmc4xslnx2863h1fwp99z7flpr66ichmz7x2fafys8gvda";
    } {};

    spoon = get {
      repo   = "spoon";
      rev    = "4424f9a";
      sha256 = "1d14qawzf7pimkjccj3f2vy9nc4fb2w00ib8li4kb180fb6wjvq4";
    } {};

    weigh = get {
      owner  = "fpco";
      repo   = "weigh";
      rev    = "26f8e3e";
      sha256 = "0pmkzlcjfqi41qmrgjyw1y7naclq86kb6mp0i4ni3d1lkiylb9gc";
    } {};
  };
};

self: super: hsPkgs {
  hackagePkg = n: v: self.callPackage (callHackage n v);

  get = { path ? null, url ? null, owner ? "Warbo", repo ? null, rev, sha256}:
    assert url == null -> repo != null || abort "Need URL or repo (${sha256})";
    with rec {
      stable  = { inherit rev sha256; };
      fullUrl = if url == null
                   then "https://github.com/${owner}/${repo}.git"
                   else url;
      git     = nix-config.latestGit { inherit stable; url = fullUrl; };
      src     = with tryEval path;
                if success && value != null then value else git;
    };
    self.callPackage (nixFromCabal (toString src) null);
}
