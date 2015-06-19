#! /usr/bin/env nix-shell
#! nix-shell -i runghc

-- Dependencies are provided by shell.nix setting "test = true"

import Control.Exception (SomeException, try)
import System.Exit
import System.Process
import System.Directory
import Test.Arbitrary.Cabal
import Test.Arbitrary.Haskell
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.QuickCheck (testProperty)

-- | Call extractAsts in a particular directory
extractAsts :: FilePath -> FilePath -> IO ExitCode
extractAsts src dest = call "extractAsts.sh" [dest] src

-- | Call a script
call script args dir = do
  cwd <- getCurrentDirectory
  (sin, sout, serr, p) <- createProcess (proc (cwd ++ "/" ++ script) []){
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

extractAstsEmpty = monadicIO $ do
  result <- run $ do rmTmpDir
                     mkDir "src"
                     mkDir "dest"
                     extractAsts (tmpDir ++ "/src") (tmpDir ++ "/dest")
  assert (result /= ExitSuccess)

main = defaultMain $ testGroup "All tests" [
           testProperty "ML4HS needs a .cabal file" ml4hsNeedsCabal
         , testProperty "Can't extractASTs from empty dir" extractAstsEmpty
         ]
