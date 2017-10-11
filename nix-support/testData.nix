{ fail, haskellPackages, haskellPkgToAsts, lib, makeHaskellPkgNixable,
  nixedHsPkg, package, runCommand, tipBenchmarks, tipToHaskellPkg, unpack,
  withNix }:

with lib;
rec {
  tip = {
    example     = ../tests/example.smt2;
    list-full   = ../benchmarks/list-full.smt2;
    nat-full    = ../benchmarks/nat-full.smt2;
    nat-simple  = ../benchmarks/nat-simple.smt2;
    teBenchmark = tipBenchmarks.tip-benchmark-smtlib;
  };

  haskellPkgs = mapAttrs (n: f: runCommand "haskell-pkg-of-${n}"
    {
      inherit f;
      buildInputs = [ fail tipToHaskellPkg ];
    }
    ''
      D=$(tipToHaskellPkg < "$f")
      [[ -e "$D" ]] || fail "'$D' doesn't exist"

      X=$(readlink -f "$D")
      [[ -d "$X" ]] || fail "'$X' isn't dir"

      ln -s "$X" "$out"
    '')
    tip // { testPackage = ../tests/testPackage; };

  haskellDrvs = mapAttrs (_: dir: haskellPackages.callPackage (nixedHsPkg dir)
                                                              {})
                         haskellPkgs //
                genAttrs [ "list-extras" ]
                         (attr: getAttr attr haskellPackages);

  asts = mapAttrs (n: drv: runCommand "asts-of-${n}"
                           {
                             src         = unpack drv.src;
                             buildInputs = [ haskellPkgToAsts ];
                           }
                           ''
                             haskellPkgToAsts "$src" > "$out"
                           '')
                  haskellDrvs;

  eqs = mapAttrs (n: asts: runCommand "eqs-of-${n}"
                             (withNix {
                               inherit asts;
                               buildInputs = [ quickspecAsts ];
                               pkg         = getAttr n haskellPkgs;
                             })
                             ''
                               quickspecAsts "$pkg" < "$asts" > "$out"
                             '')
                 asts;
}
