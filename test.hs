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

extractAsts :: FilePath -> FilePath -> IO ExitCode
extractAsts src dest = call "extractAsts.sh" [dest] src

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

cabalProjectsWork p = monadicIO $ withProject p tryAsts
  where tryAsts dir = do result <- run $ do mkDir "asts"
                                            extractAsts dir (tmpDir ++ "/asts")
                         assert (result == ExitSuccess)

ml4hsNeedsCabal = monadicIO $ do code <- run $ rawSystem "./ml4hs.sh" ["/"]
                                 assert (code /= ExitSuccess)

mkDir path = createDirectoryIfMissing True (tmpDir ++ "/" ++ path)

extractAstsEmpty = monadicIO $ do
  result <- run $ do rmTmpDir
                     mkDir "src"
                     mkDir "dest"
                     extractAsts (tmpDir ++ "/src") (tmpDir ++ "/dest")
  assert (result == ExitSuccess)

cabalGetsAsts p = not (null (files p)) ==>
  monadicIO $ withProject p checkAsts
  where checkAsts dir = do
          result <- run $ do
            mkDir "asts"
            extractAsts dir (tmpDir ++ "/asts")
            contents <- getDirectoryContents (tmpDir ++ "/asts")
            let noDots = filter (not . ("." `isPrefixOf`)) contents
            return noDots
          assert (not (null result))

withOptions = localOption (QuickCheckTests 10)

main = defaultMain $ withOptions $ testGroup "All tests" [
           testProperty "ML4HS needs a .cabal file" ml4hsNeedsCabal
         , testProperty "Can extractASTs from empty dir" extractAstsEmpty
         , testProperty "Can extract ASTs from Cabal project" cabalProjectsWork
         , testProperty "Have ASTs" cabalGetsAsts
         ]
