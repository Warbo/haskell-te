{ buckets, buildEnv, hashspecBench, haskellPkgToAsts, mlspecBench, quickspec,
  quickspecAsts, stdenv, tipBenchmarks }:

buildEnv {
  name  = "haskell-te";
  paths = [
    quickspec
    quickspecAsts
    haskellPkgToAsts
  ];
}
