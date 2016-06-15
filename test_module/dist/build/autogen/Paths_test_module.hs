module Paths_test_module (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/chris/.cabal/bin"
libdir     = "/home/chris/.cabal/lib/i386-linux-ghc-7.10.3/test-module-0.1.0.0-HRXGicJxXDv5oD4TUfibhS"
datadir    = "/home/chris/.cabal/share/i386-linux-ghc-7.10.3/test-module-0.1.0.0"
libexecdir = "/home/chris/.cabal/libexec"
sysconfdir = "/home/chris/.cabal/etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "test_module_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "test_module_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "test_module_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "test_module_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "test_module_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
