{ buckets, buildEnv, hashspecBench, haskellPkgToAsts, mlspecBench, quickspec,
  quickspecAsts, stdenv, tipBenchmarks }:

buildEnv {
  name  = "haskell-theory-exploration";
  paths = [
    quickspec
    quickspecAsts
    haskellPkgToAsts
    mlspecBench.mls
  ];
}
