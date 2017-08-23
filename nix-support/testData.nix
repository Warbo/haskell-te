{ haskellPkgToAsts, lib, runCommand, tipBenchmarks, tipToHaskellPkg }:

with lib;
rec {
  tip = {
    example     = ../tests/example.smt2;
    list-full   = ../benchmarks/list-full.smt2;
    nat-full    = ../benchmarks/nat-full.smt2;
    nat-simple  = ../benchmarks/nat-simple.smt2;
    teBenchmark = tipBenchmarks.tip-benchmark-smtlib;
  };

  haskellPkgs = (mapAttrs (n: f: runCommand "haskell-pkg-of-${n}"
                                   {
                                     inherit f;
                                     buildInputs = [ tipToHaskellPkg ];
                                   }
                                   ''
                                     D=$(tipToHaskellPkg < "$f")
                                     ln -s "$D" "$out"
                                   '')
                          tip) // { testPackage = ../tests/testPackage; };

  asts = mapAttrs (n: p: runCommand "asts-of-${n}"
                           {
                             inherit p;
                             buildInputs = [ haskellPkgToAsts ];
                           }
                           ''
                             haskellPkgToAsts "$p" > "$out"
                           '')
                  haskellPkgs;
}
