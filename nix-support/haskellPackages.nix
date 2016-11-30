{ callHackage, extractTarball, fetchFromGitHub, fetchgit, fetchurl, haskell,
  havePath, lib, nixFromCabal, superHaskellPackages }:

with builtins;
with lib;

assert let got    = superHaskellPackages.ghc.version;
           should = "7.10.3";
        in got == should || abort "Using GHC ${got} (should be ${should})";
rec {

hsOverride = self: super:
  # Use nixFromCabal on paths in ../packages
  let optimise   = pkg: haskell.lib.overrideCabal pkg (oldAttrs: {
        configureFlags = [ "--ghc-option=-O2" ];
      });
      cabalPath  = p: self.callPackage (nixFromCabal (toString p) null);
      cabalCheck = name: given: fallback: cabalPath (if havePath name
                                                        then given
                                                        else fallback);
   in mapAttrs (_: optimise) {
        AstPlugin         = cabalCheck "ast-plugin"
                                       <ast-plugin>
                                       (fetchFromGitHub {
                                         owner  = "Warbo";
                                         repo   = "ast-plugin";
                                         rev    = "a04f6fef18bdd6d23d534ea4dd7c7b5b9084ad1c";
                                         sha256 = "1gmkv4l38vpvhg2h8dwv4gf8dq1d0lr0zxd5j9szi90xb8nl2241";
                                       })
                                       {};

        bench             = cabalPath (extractTarball (fetchurl {
                              url    = https://github.com/Gabriel439/bench/archive/1.0.1.tar.gz;
                              sha256 = "1amfq2jhwxzy34gyqyvanc46admwlfqs9dk3d7c10aivbl7v1kyb";
                            })) {};

        GetDeps           = cabalCheck "get-deps" <get-deps>
                                       (fetchFromGitHub {
                                         owner  = "Warbo";
                                         repo   = "getDeps";
                                         rev    = "7c02fbc9b0076f0327d95c3aa05cb607a2f3cf73";
                                         sha256 = "19g1lyaplclnlyh7y3li08937bqgk58dsblz12hd290crmg999f0";
                                       })
                                       {};

        HS2AST            = cabalCheck "hs2ast" <hs2ast>
                                       (fetchFromGitHub {
                                         owner  = "Warbo";
                                         repo   = "hs2ast";
                                         rev    = "469d99977a78484159a7f5f77f8fbeeeea2b33a4";
                                         sha256 = "1x2f12s6caj0gaymaw62bmm62ydim78wm2pn18j18fa2l3p7vqyi";
                                       })
                                       {};

        ifcxt             = cabalCheck "ifcxt" <ifcxt>
                                       (fetchFromGitHub {
                                         owner  = "mikeizbicki";
                                         repo   = "ifcxt";
                                         rev    = "7f9f876807f33f8fc84d0face54171ebcca57a4a";
                                         sha256 = "0mzd5h45rkvj81pdi60p68r0j3lc4h9m4z3b4v8m6xacp9sxiic1";
                                       })
                                       {};

        ML4HSFE           = cabalCheck "ml4hsfe" <ml4hsfe>
                                       (fetchFromGitHub {
                                         owner  = "Warbo";
                                         repo   = "ml4hsfe";
                                         rev    = "bcdd93b64ae5503d93f1e56ce9cba44004f2ddaa";
                                         sha256 = "1ca59xp5mq2bv4kbml32k4xgql03bqi6b4s7pvzdah9fsi76ap6q";
                                       })
                                       {};

        mlspec            = cabalCheck "mlspec" <mlspec>
                                       (fetchFromGitHub {
                                         owner  = "Warbo";
                                         repo   = "mlspec";
                                         rev    = "3a746aa36e48b24c2d66b337512b9d5ac33c69ee";
                                         sha256 = "12c7x9pabd3ww91rq2riq185n1i1sd658dr3jm65yriql5a23fs4";
                                       })
                                       {};

        mlspec-helper     = cabalCheck "mlspec-helper"
                                       <mlspec-helper>
                                       (fetchFromGitHub {
                                         owner  = "Warbo";
                                         repo   = "mlspec-helper";
                                         rev    = "1bf9c32e3ec0e519237a0af297d6512907e95959";
                                         sha256 = "1g8jwbfdqa84xdh6gp8ica4v0l51jki880fwmmhs3fcl4vz6i4ax";
                                       })
                                       {};

        nix-eval          = cabalCheck "nix-eval"
                                       <nix-eval>
                                       (fetchFromGitHub {
                                         owner  = "Warbo";
                                         repo   = "nix-eval";
                                         rev    = "2892a2cf2fbbf7275ffdf722059fb0399fc8ca49";
                                         sha256 = "1wssn7grrwwg1pl1z6s6w73wkdn70mm1dbz98sr9r5crliwyf585";
                                       })
                                       {};

        reduce-equations  = cabalCheck "reduce-equations"
                                       <reduce-equations>
                                       (fetchFromGitHub {
                                         owner  = "Warbo";
                                         repo   = "reduce-equations";
                                         rev    = "a86199b68e5a3513cc3cf0e579d67ea6cfa311ae";
                                         sha256 = "1ncy2carn18fcwpfdfch99b90mwq52a7dal8rn5kv1wk3951w5rg";
                                       })
                                       {
                                         haskell-src-exts = self.callPackage (callHackage "haskell-src-exts" "1.19.0") {
                                           pretty-show    = self.callPackage (callHackage "pretty-show"      "1.6.12") {};
                                         };
                                       };

        runtime-arbitrary = cabalCheck "runtime-arbitrary"
                                       <runtime-arbitrary>
                                       (fetchFromGitHub {
                                         owner  = "Warbo";
                                         repo   = "runtime-arbitrary";
                                         rev    = "dc722289226520019307f9bfe000b378630e9d6c";
                                         sha256 = "001v1k6m56kik18jcccygwa7k5wc49j2gbpk9hj2n7pgrk3nfady";
                                       })
                                       {};

        weigh             = cabalPath (fetchgit {
                              url    = https://github.com/fpco/weigh.git;
                              rev    = "26f8e3e";
                              sha256 = "0pmkzlcjfqi41qmrgjyw1y7naclq86kb6mp0i4ni3d1lkiylb9gc";
                            }) {};
      };

haskellPackages = superHaskellPackages.override { overrides = hsOverride; };

}
