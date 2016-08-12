defs: with defs; with builtins;

let env = {
      buildInputs = [ (haskellPackages.ghcWithPackages (p: [
                        (nixFromCabal (toString tipBenchmarks.tip-benchmarks)
                                      null)
                      ])) ];
    };

 in {} #testRun "Can build TIP module" null env "exit 0"
