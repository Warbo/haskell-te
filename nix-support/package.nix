{ buckets, buildEnv, hashspecBench, mlspecBench, quickspec, stdenv,
  tipBenchmarks }:

with {
  env = buildEnv {
    name  = "te-env";
    paths = [ tipBenchmarks.tools ];
  };
};
buildEnv {
  name  = "haskell-te";
  paths = [
    quickspec mlspecBench.mls hashspecBench.hs buckets.hashes
  ];
}
