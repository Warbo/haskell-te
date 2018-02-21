{ callPackage, latestGit, runCommand, tryElse, writeScript }:

with builtins;
with rec {
  path = tryElse <te-benchmarks> (latestGit {
    url    = http://chriswarbo.net/git/theory-exploration-benchmarks.git;
    stable = {
      rev    = "e993b2f";
      sha256 = "0zwd2bynj645b5frvmkb9mc4fhvvqv25ls6sh56wwaq69a5k76rq";
    };
  });

  tebench = callPackage path {};
};
{
  inherit tebench;
  inherit (tebench) tip-benchmark-haskell tip-benchmark-smtlib tools;

  # Useful for tests. Defining it here means we don't have to expose path, env,
  # etc.
  commDeps = runCommand "commDeps"
               (tebench.cache // {
                 getCommDeps = writeScript "getCommDeps.rkt" ''
                   #lang racket
                   (require lib/normalise)
                   (require lib/theorems)
                   (for ([dep (theorem-deps-of "tip2015/bin_plus_comm.smt2")])
                        (write (encode-lower-name dep)))
                 '';
                 buildInputs = [ tebench.env ];
               })
               ''
                 set -e
                 racket "$getCommDeps" > "$out"
               '';
}
