{ buckets, buildEnv, hashspecBench, mlspecBench, quickspecBench,
  stdenv, tipBenchmarks }:

let env = buildEnv {
      name  = "te-env";
      paths = [ tipBenchmarks.tools ];
    };
 in buildEnv {
      name  = "haskell-te";
      paths = [
        quickspecBench.qs mlspecBench.mls hashspecBench.hs
        buckets.hashes
      ];
    }
