#! /usr/bin/env nix-shell
#! nix-shell -i runghc

-- Dependencies are provided by shell.nix

import Control.Exception (SomeException, try)
import Data.List
import System.Exit
import System.Process
import System.Directory
import Test.Arbitrary.Cabal
import Test.Arbitrary.Haskell
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Test.Tasty (defaultMain, testGroup, localOption)
import Test.Tasty.QuickCheck

--ml4hs src = call "ml4hs.sh" src

-- | Call a script, with arguments args and working directory dir
call script args dir = do
  cwd <- getCurrentDirectory
  (sin, sout, serr, p) <- createProcess (proc (cwd ++ "/" ++ script) args){
                                           cwd = Just dir
                                         }
  waitForProcess p

tmpDir = "/tmp/ML4HSTest"

rmTmpDir :: IO (Either SomeException ())
rmTmpDir = try (removeDirectoryRecursive tmpDir)

withProject :: Project -> (FilePath -> PropertyM IO a) -> PropertyM IO a
withProject p f = do dir <- run $ makeProject tmpDir p
                     result <- f dir
                     run rmTmpDir
                     return result

ml4hsNeedsCabal = monadicIO $ do code <- run $ rawSystem "./ml4hs.sh" ["/"]
                                 assert (code /= ExitSuccess)

mkDir path = createDirectoryIfMissing True (tmpDir ++ "/" ++ path)

withOptions = localOption (QuickCheckTests 10)

main = defaultMain $ withOptions $ testGroup "All tests" [
         ]
