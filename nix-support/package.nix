{ buildEnv, haskellPkgToAsts, quickspec, quickspecAsts }:

buildEnv {
  name  = "haskell-theory-exploration";
  paths = [
    quickspec
    quickspecAsts
    (haskellPkgToAsts {})
  ];
}
