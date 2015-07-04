#!/usr/bin/env runhaskell

{-# LANGUAGE OverloadedStrings #-}

import Data.Maybe
import System.Environment
import qualified Data.Attoparsec       as A
import qualified Data.ByteString       as B
import qualified Data.ByteString.Char8 as C
import qualified Data.AttoLisp         as L
import qualified Data.Stringable       as S
import qualified Data.Text             as T

-- To minimise headaches, we try to use s-expressions for data interchange.
-- We use types, parsers and pretty-printers from AttoLisp, which forces us to
-- juggle Strings, ByteStrings and Text using toString and fromString.

main = do args <- getArgs
          interact (run args)

run :: [String] -> String -> String
run args stdin = cmd stdin
  where cmd :: String -> String
        cmd = case args of
          ["typeCommand"] -> typeCommand
          ["ordCommand"]  -> ordCommand
          ["renderAsts"]  -> renderCommand
          _               -> error $ "Unknown arguments '" ++ show args ++ "'"

-- Build a command for GHCi to inspect the type of each name
-- The ":m" unloads everything except Prelude, ensuring that names all get
-- qualified and we can't see any non-exported members
typeCommand = S.toString .
              T.unlines  .
              (":m":)    .
              map cmd    .
              parseLisps .
              S.fromString
  where cmd s = T.concat [":t (", getQName s, ")"]

-- Try to partially-apply ">" to each value, to see if it admits an instance
-- of Ord
ordCommand = S.toString  .
             T.unlines   .
             (":m":)     .
             map ordLine .
             T.lines     .
             S.fromString

renderCommand = unlines        .
                map show       .
                renderCommand' .
                parseLisps     .
                S.fromString

renderCommand' ls = [giveType ast t | ast <- asts, t <- sigNamed (getQName ast)]
  where asts = filter isAst ls
        sigs = filter isSig ls
        sigName (L.List (L.String "::":L.String n:_)) = n
        sigNamed n = filter ((== n) . sigName) sigs

giveType line sig = cons id' (cdr line)
  where id  = nth 0 line
        id' = snoc (cdr id) typ  -- Drop "FOUNDAST" and append type
        typ = nth 2 sig

-- | (("FOUNDAST" ...) ...)
isAst (L.List (L.List (L.String "FOUNDAST":_):_)) = True
isAst _                                           = False

-- | ("::" "name" "type")
isSig (L.List (L.String "::":_)) = True
isSig _                          = False

ordLine x = T.concat [":t (", applyTo ">" result, ")"]
  where [name, typeStr] = T.splitOn " :: " x
        typeExpr = typeLisp (reString typeStr)
        result   = addArgs name (arity typeExpr)

arity (L.List xs) = length xs - 1

applyTo x y = T.concat ["(", x, ") (", y, ")"]

addArgs x 0 = x
addArgs x n = addArgs (applyTo x "undefined") (n-1)

-- | Unwrap spurious parens "(((foo)))" into "foo"
unParen "" = ""
unParen x  = if head x == '(' && last x == ')'
                then unParen (init (tail x))
                else x

-- | Parse Haskell types "a -> (b -> IO c) -> d" into ("a" ("b" "IO c") "d")
typeLisp s = case typeList s of
                  [t] -> L.toLisp [t]
                  ts  -> L.toLisp (map typeLisp ts)

-- | Turns "a -> (b -> c) -> d" into ["a", "(b -> c)", "d"]
typeList = reverse . map reverse . typeList' 0 [""] . unParen

-- | Parse one "level" of Haskell type syntax, eg. "a -> (b -> c) -> d" becomes
-- ["a", "b -> c", "d"]. In fact it's reversed: ["d", "c >- b", "a"]
typeList' :: Int -> [String] -> String -> [String]
typeList' _    ts  "" = ts                                 -- Base case
typeList' l (t:ts) s  = uncurry3 typeList' $ case s of
  '(':')':s'         -> (l,   ("()"++t):ts,           s')  -- Keep unit types
  '(':s'             -> (l+1, ('(':t):ts,             s')  -- Track nesting
  ')':s'             -> (l-1, (')':t):ts,             s')  -- Track nesting
  ' ':'-':'>':' ':s' -> (l,   if l == 0                    -- Are we at the top-level?
                                 then "":t:ts              -- Start a new entry
                                 else (" >- "++t):ts, s')  -- Remember the "->"
  c:s'               -> (l,   (c:t):ts,               s')  -- Remember any other Char

uncurry3 f (a, b, c) = f a b c

parseLisp  = A.maybeResult . A.parse L.lisp
parseLisps = mapMaybe parseLisp . C.split '\n'

nth  i (L.List xs)   = xs !! i
car                  = nth 0
cdr    (L.List xs)   = L.List (tail xs)
cons x (L.List xs)   = L.List (x:xs)
snoc   (L.List xs) x = L.List (xs ++ [x])

-- | Input has the form (id ast), where id may have many components

unString (L.String x) = x
getId      = nth 0
getAst     = nth 1
getPkg     = unString . nth 1 . getId
getMod     = unString . nth 2 . getId
getName    = unString . nth 3 . getId
getQName x = let m = getMod x
                 n = getName x
             in  T.concat [m, ".", n]

reString :: (S.Stringable a, S.Stringable b) => a -> b
reString = S.fromString . S.toString
