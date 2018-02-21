{ callHackage, latestGit, lib, nixedHsPkg, stable }:

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

    GetDeps = get {
      path   = <get-deps>;
      repo   = "getDeps";
      rev    = "7c02fbc";
      sha256 = "19g1lyaplclnlyh7y3li08937bqgk58dsblz12hd290crmg999f0";
    } {};

    HS2AST = get {
      path   = <hs2ast>;
      repo   = "hs2ast";
      rev    = "469d999";
      sha256 = "1x2f12s6caj0gaymaw62bmm62ydim78wm2pn18j18fa2l3p7vqyi";
    } {};

    ifcxt = get {
      path   = <ifcxt>;
      owner  = "mikeizbicki";
      repo   = "ifcxt";
      rev    = "7f9f876";
      sha256 = "0mzd5h45rkvj81pdi60p68r0j3lc4h9m4z3b4v8m6xacp9sxiic1";
    } {};

    ML4HSFE = get {
      path   = <ml4hsfe>;
      repo   = "ml4hsfe";
      rev    = "ecbc833";
      sha256 = "0sgkc6kbyiilv4hs1485lrhbb2ja06bg9yrzd3kylw4l4jlk9lmn";
    } {};

    mlspec = get {
      path   = <mlspec>;
      repo   = "mlspec";
      rev    = "8f97e7f";
      sha256 = "1ay4zw55k659cdpg1mbb3jcdblabyajpj657v4fc6wvydqvia6d5";
    } {};

    mlspec-helper = get {
      path   = <mlspec-helper>;
      repo   = "mlspec-helper";
      rev    = "d794706";
      sha256 = "0vlr3ar1zwk0ykbzmg47j1yv1ba8gf6nzqj10bfy60nii91z7slh";
    } {};

    nix-eval = get {
      path   = <nix-eval>;
      repo   = "nix-eval";
      rev    = "53d18a2";
      sha256 = "0rplpygiqn6f9aqi09dr67xidb1bks9xnxxrpzi3bq67bdvjzvh1";
    } {};

    reduce-equations = get {
      path   = <reduce-equations>;
      repo   = "reduce-equations";
      rev    = "111af37";
      sha256 = "14164562v6w151qxzrhilxacd1xwb48qf7l39nfzf313vw6qj3xc";
    } {
      haskell-src-exts = hackagePkg "haskell-src-exts" "1.19.0" {
        pretty-show = hackagePkg "pretty-show" "1.6.12" {};
      };
    };

    runtime-arbitrary = get {
      path   = <runtime-arbitrary>;
      repo   = "runtime-arbitrary";
      rev    = "5b7ff2f";
      sha256 = "11gnfmz48vxvf42xs9255r51vbv1sjghvzi60gcrpx3jk38d2gyb";
    } {};

    spoon = get {
      repo   = "spoon";
      rev    = "4424f9a";
      sha256 = "14mn6ygr0wqy4css8wrbxd6b4qvp951xgc206x79fjfva3q6n12g";
    } {};
  };
};

extra: self: super: hsPkgs {
  hackagePkg = n: v: self.callPackage (callHackage n v);

  get = { path ? null, url ? null, owner ? "Warbo", repo ? null, rev, sha256}:
    assert url == null -> repo != null || abort "Need URL or repo (${sha256})";
    with rec {
      stable  = { inherit rev sha256; };
      fullUrl = if url == null
                   then "https://github.com/${owner}/${repo}.git"
                   else url;
      git     = latestGit { inherit stable; url = fullUrl; };
      src     = with tryEval path;
                if success && value != null then value else git;
    };
    self.callPackage (nixedHsPkg (toString src));
} // extra self super
