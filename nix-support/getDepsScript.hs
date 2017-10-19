{-# LANGUAGE OverloadedStrings #-}
import           Control.Lens
import           Data.Aeson
import           Data.Aeson.Lens
import qualified Data.ByteString as BS
import           Data.Char
import           Data.List
import           Data.Semigroup
import           Data.Text.Lens
import           Data.Validation

import qualified GetDeps
import qualified SexprHelper
import qualified Types as GD.Types

-- Acts like `Either [String] a`, but combines the content
type OrErrors = AccValidation [String]

instance (Semigroup e) => Monad (AccValidation e) where
  return = pure
  (AccSuccess x) >>= f = f x
  (AccFailure e) >>= f = AccFailure e

-- Read stdin as a JSON array, apply addDeps to each entry and send to stdout
main :: IO ()
main = BS.interact (over _Array go)
  where go vs = case traverse addDeps vs of
                     AccFailure errs -> error (unlines (msg:errs))
                     AccSuccess vs'  -> vs'
        msg   = "getDepsScript: aborting due to errors"

-- Add a "dependencies" field containing this entry's dependencies
addDeps :: Value -> OrErrors Value
addDeps v = add <$> deps v
  where add ds = v & _Object . at "dependencies" ?~ toJSON ds

-- Looks up the dependencies of an entry, and formats them
deps :: Value -> OrErrors [Value]
deps v = rawDeps v >>= traverse formatDep

-- Looks up the "ast" field of an entry, traverses it looking for global
-- names and deduplicates the resulting list
rawDeps :: Value -> OrErrors [GD.Types.Out]
rawDeps v = case v ^? key "ast" . _String . unpacked of
                 Nothing -> AccFailure ["No 'ast' in " ++ show v]
                 Just a  -> AccSuccess (deps' a)
  where deps' = nub . GetDeps.getDeps . SexprHelper.parseSexpr

-- Split package fields like "foo-1.2" into package "foo" and version "1.2"
formatDep :: GD.Types.Out -> OrErrors Value
formatDep o = case pair of
                   Nothing     -> AccFailure ["No 'package' in " ++ show dep]
                   Just (p, v) -> AccSuccess $ case v of
                     Just v' -> dep & setP .~ p & setV .~ v'
                     Nothing -> dep & setP .~ p
  where dep  = toJSON o
        pair = dep ^? key "package" . _String . unpacked . to splitOffVersion
        setP = _Object . at "package" . _Just . _String . unpacked
        setV = _Object . at "version" . _Just . _String . unpacked

-- Splits the version off a package name (if any)
splitOffVersion :: String -> (String, Maybe String)
splitOffVersion raw = if "-" `isPrefixOf` version
                         then (name, Just (tail version))
                         else (raw,  Nothing)
  where (name, version) = (reverse n, reverse v)
        (v,    n)       = span versionic (reverse raw)
        versionic c     = isNumber c || c `elem` ['-', '.']
