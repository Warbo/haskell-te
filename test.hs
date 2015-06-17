#! /usr/bin/env nix-shell
#! nix-shell -i runghc

-- Dependencies are provided by shell.nix setting "test = true"

import System.Exit
import System.Process
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.QuickCheck (testProperty)


ml4hsNeedsCabal = monadicIO $ do code <- run $ rawSystem "./ml4hs.sh" ["/"]
                                 assert (code /= ExitSuccess)

main = defaultMain $ testGroup "All tests" [
         testProperty "ML4HS needs a .cabal file" ml4hsNeedsCabal
       ]
