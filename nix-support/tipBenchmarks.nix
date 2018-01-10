{ asv-nix, callPackage, haskellPackages, nix-config, nix-config-src, runCommand,
  tryElse, writeScript }:

with builtins;
with rec {
  path = tryElse <te-benchmarks> (nix-config.latestGit {
    url    = http://chriswarbo.net/git/theory-exploration-benchmarks.git;
    stable = {
      rev    = "481b722";
      sha256 = "0jl7f5s983sxz9g58pf80iywzkcn74m1ns2w21f3x81xpkcqspaw";
    };
  });

  tebench = callPackage path {
    inherit asv-nix haskellPackages nix-config-src;

    # Nixpkgs 17.03 disables Racket on i686, so always use 16.09 (for now)
    pkgsPath = nix-config.repo1609;
  };
};
{
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
