defs: with defs; with builtins;

let env = {
      buildInputs = [
        (haskellPackages.ghcWithPackages (p: [
          (p.callPackage tipBenchmarks.pkgDef {})
        ]))
      ];
    };

 in testRun "Can build TIP module" null env "exit 0"
