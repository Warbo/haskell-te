defs: with defs;

testMsg (parseJSON (runScript { buildInputs = [
                      (haskellPackages.ghcWithPackages (h: [
                        tipBenchmarks.pkg
                      ]))
                      cabal-install
                    ]; } ''
   export HOME="$PWD"
   pushd "${tipBenchmarks.path}"

   if ./test.sh
   then
     echo "true"  > "$out"
   else
     echo "false" > "$out"
   fi
'')) "Tip benchmark tests pass"
