defs: with defs; with builtins;

rec {

  env =  {
           buildInputs = [
                           (haskellPackages.ghcWithPackages (p: [
                             (nixFromCabal (toString tipBenchmarks.module) null)
                           ]))
                         ];
         };

  result = runScript env ''
             echo -e 'import A\nmain = print "true"' | runhaskell > "$out"
           '';

 test = testMsg (parseJSON result) "Can build TIP module";

}.test
