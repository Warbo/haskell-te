{ buildEnv, concurrentQuickspec, haskellPkgToAsts, quickspec, quickspecAsts,
  renderEqs, tipToHaskellPkg }:

buildEnv {
  name  = "haskell-theory-exploration";
  paths = [
    concurrentQuickspec
    (haskellPkgToAsts {})
    quickspec
    quickspecAsts
    renderEqs
    tipToHaskellPkg
  ];
}
