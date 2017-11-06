{ buildEnv, concurrentQuickspec, haskellPkgToAsts, quickspec, quickspecAsts,
  reduce-equations, renderEqs, tipToHaskellPkg }:

buildEnv {
  name  = "haskell-theory-exploration";
  paths = [
    concurrentQuickspec
    (haskellPkgToAsts {})
    quickspec
    quickspecAsts
    reduce-equations
    renderEqs
    tipToHaskellPkg
  ];
}
