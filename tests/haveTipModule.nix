defs: with defs; with builtins;

let env = {
      buildInputs = [ (haskellPackages.ghcWithPackages (p: [
                        (nixFromCabal (toString tipBenchmarks.module) null)
                      ])) ];
    };

 in testRun "Can build TIP module" null env "exit 0"
