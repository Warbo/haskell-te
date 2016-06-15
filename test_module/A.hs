{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
module A where
import qualified Text.Show.Functions
import qualified Data.Typeable as T
import qualified Prelude as P
import qualified Test.QuickSpec as QS
import qualified Test.Feat as F
import qualified Test.QuickCheck as QC
data Grammarssimpexprunambig3smt2list a =
  Nil | Cons a (Grammarssimpexprunambig3smt2list a)
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Grammarssimpexprunambig3smt2list)
instance
  (F.Enumerable a) =>
    QC.Arbitrary (Grammarssimpexprunambig3smt2list a)
  where
  arbitrary = QC.sized F.uniform
data Grammarssimpexprunambig3smt2Tok =
  Grammarssimpexprunambig3smt2C | Grammarssimpexprunambig3smt2D |
  Grammarssimpexprunambig3smt2X | Grammarssimpexprunambig3smt2Y |
  Grammarssimpexprunambig3smt2Pl
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Grammarssimpexprunambig3smt2Tok)
instance QC.Arbitrary Grammarssimpexprunambig3smt2Tok where
  arbitrary = QC.sized F.uniform
data Grammarssimpexprunambig3smt2E =
  Grammarssimpexprunambig3smt2Plus
    Grammarssimpexprunambig3smt2E Grammarssimpexprunambig3smt2E |
  EX | EY
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Grammarssimpexprunambig3smt2E)
instance QC.Arbitrary Grammarssimpexprunambig3smt2E where
  arbitrary = QC.sized F.uniform
data Grammarssimpexprunambig5smt2T = TX | TY
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Grammarssimpexprunambig5smt2T)
instance QC.Arbitrary Grammarssimpexprunambig5smt2T where
  arbitrary = QC.sized F.uniform
data Grammarssimpexprunambig5smt2E =
  Grammarssimpexprunambig5smt2Plus
    Grammarssimpexprunambig5smt2T Grammarssimpexprunambig5smt2E |
  Grammarssimpexprunambig5smt2Term Grammarssimpexprunambig5smt2T
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Grammarssimpexprunambig5smt2E)
instance QC.Arbitrary Grammarssimpexprunambig5smt2E where
  arbitrary = QC.sized F.uniform
data GrammarspackratunambigPackratsmt2Tok =
  GrammarspackratunambigPackratsmt2X |
  GrammarspackratunambigPackratsmt2Y |
  GrammarspackratunambigPackratsmt2Z
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''GrammarspackratunambigPackratsmt2Tok)
instance QC.Arbitrary GrammarspackratunambigPackratsmt2Tok where
  arbitrary = QC.sized F.uniform
data B2 = GrammarspackratunambigPackratsmt2SB B2 | ZB
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''B2)
instance QC.Arbitrary B2 where arbitrary = QC.sized F.uniform
data GrammarspackratunambigPackratsmt2S =
  GrammarspackratunambigPackratsmt2A B2 |
  GrammarspackratunambigPackratsmt2B B2
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''GrammarspackratunambigPackratsmt2S)
instance QC.Arbitrary GrammarspackratunambigPackratsmt2S where
  arbitrary = QC.sized F.uniform
data Isaplannerprop54smt2Nat =
  Isaplannerprop54smt2Z |
  Isaplannerprop54smt2S Isaplannerprop54smt2Nat
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Isaplannerprop54smt2Nat)
instance QC.Arbitrary Isaplannerprop54smt2Nat where
  arbitrary = QC.sized F.uniform
data Isaplannerprop45smt2Pair b c = Pair2 b c
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Isaplannerprop45smt2Pair)
instance
  (F.Enumerable b, F.Enumerable c) =>
    QC.Arbitrary (Isaplannerprop45smt2Pair b c)
  where
  arbitrary = QC.sized F.uniform
data Isaplannerprop47smt2Tree a2 =
  Leaf |
  Isaplannerprop47smt2Node
    (Isaplannerprop47smt2Tree a2) a2 (Isaplannerprop47smt2Tree a2)
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Isaplannerprop47smt2Tree)
instance
  (F.Enumerable a2) => QC.Arbitrary (Isaplannerprop47smt2Tree a2)
  where
  arbitrary = QC.sized F.uniform
data Tip2015intaddassocsmt2Integer =
  Tip2015intaddassocsmt2P Isaplannerprop54smt2Nat |
  Tip2015intaddassocsmt2N Isaplannerprop54smt2Nat
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Tip2015intaddassocsmt2Integer)
instance QC.Arbitrary Tip2015intaddassocsmt2Integer where
  arbitrary = QC.sized F.uniform
data Tip2015regexpRecPlussmt2R =
  Tip2015regexpRecPlussmt2Nil | Eps |
  Tip2015regexpRecPlussmt2Atom Grammarssimpexprunambig5smt2T |
  Tip2015regexpRecPlussmt2Plus
    Tip2015regexpRecPlussmt2R Tip2015regexpRecPlussmt2R |
  Tip2015regexpRecPlussmt2Seq
    Tip2015regexpRecPlussmt2R Tip2015regexpRecPlussmt2R |
  Tip2015regexpRecPlussmt2Star Tip2015regexpRecPlussmt2R
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Tip2015regexpRecPlussmt2R)
instance QC.Arbitrary Tip2015regexpRecPlussmt2R where
  arbitrary = QC.sized F.uniform
data Tip2015treesortAddSamesmt2Tree a3 =
  Tip2015treesortAddSamesmt2Node
    (Tip2015treesortAddSamesmt2Tree a3) a3
    (Tip2015treesortAddSamesmt2Tree a3) |
  Tip2015treesortAddSamesmt2Nil
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Tip2015treesortAddSamesmt2Tree)
instance
  (F.Enumerable a3) =>
    QC.Arbitrary (Tip2015treesortAddSamesmt2Tree a3)
  where
  arbitrary = QC.sized F.uniform
data Tip2015heapSortPermutessmt2Heap =
  Tip2015heapSortPermutessmt2Node
    Tip2015heapSortPermutessmt2Heap Isaplannerprop54smt2Nat
    Tip2015heapSortPermutessmt2Heap |
  Tip2015heapSortPermutessmt2Nil
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Tip2015heapSortPermutessmt2Heap)
instance QC.Arbitrary Tip2015heapSortPermutessmt2Heap where
  arbitrary = QC.sized F.uniform
data Bin =
  Tip2015binplussmt2One | Tip2015binplussmt2ZeroAnd Bin |
  Tip2015binplussmt2OneAnd Bin
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Bin)
instance QC.Arbitrary Bin where arbitrary = QC.sized F.uniform
data Token =
  Tip2015escapeNoSpecialsmt2A | Tip2015escapeNoSpecialsmt2B |
  Tip2015escapeNoSpecialsmt2C | Tip2015escapeNoSpecialsmt2D | ESC |
  Tip2015escapeNoSpecialsmt2P | Tip2015escapeNoSpecialsmt2Q |
  Tip2015escapeNoSpecialsmt2R
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Token)
instance QC.Arbitrary Token where arbitrary = QC.sized F.uniform
data Tip2015substSubstFreeYessmt2Expr =
  Tip2015substSubstFreeYessmt2Var P.Int |
  Tip2015substSubstFreeYessmt2Lam
    P.Int Tip2015substSubstFreeYessmt2Expr |
  Tip2015substSubstFreeYessmt2App
    Tip2015substSubstFreeYessmt2Expr Tip2015substSubstFreeYessmt2Expr
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Tip2015substSubstFreeYessmt2Expr)
instance QC.Arbitrary Tip2015substSubstFreeYessmt2Expr where
  arbitrary = QC.sized F.uniform
data Maybe a4 = Nothing | Tip2015heapdeleteMinimumsmt2Just a4
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Maybe)
instance (F.Enumerable a4) => QC.Arbitrary (Maybe a4) where
  arbitrary = QC.sized F.uniform
data Tip2015substSubstFreeNosmt2Expr =
  Tip2015substSubstFreeNosmt2Var P.Int |
  Tip2015substSubstFreeNosmt2Lam
    P.Int Tip2015substSubstFreeNosmt2Expr |
  Tip2015substSubstFreeNosmt2App
    Tip2015substSubstFreeNosmt2Expr Tip2015substSubstFreeNosmt2Expr
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Tip2015substSubstFreeNosmt2Expr)
instance QC.Arbitrary Tip2015substSubstFreeNosmt2Expr where
  arbitrary = QC.sized F.uniform
data Tip2015polyrecseqindexsmt2Seq a5 =
  Tip2015polyrecseqindexsmt2Nil |
  Tip2015polyrecseqindexsmt2Cons
    a5
    (Tip2015polyrecseqindexsmt2Seq
       (Isaplannerprop45smt2Pair a5 (Maybe a5)))
  deriving (P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Tip2015polyrecseqindexsmt2Seq)
instance
  (F.Enumerable a5) =>
    QC.Arbitrary (Tip2015polyrecseqindexsmt2Seq a5)
  where
  arbitrary = QC.sized F.uniform
append ::
  Grammarssimpexprunambig3smt2list a6 ->
    Grammarssimpexprunambig3smt2list a6 ->
      Grammarssimpexprunambig3smt2list a6
append Nil y = y
append (Cons z xs) y = Cons z (append xs y)
grammarssimpexprunambig3smt2lin ::
  Grammarssimpexprunambig3smt2E ->
    Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok
grammarssimpexprunambig3smt2lin
  (Grammarssimpexprunambig3smt2Plus a7 b2) =
  append
    (append
       (append
          (Cons
             Grammarssimpexprunambig3smt2C
             (Nil ::
                Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok))
          (grammarssimpexprunambig3smt2lin a7))
       (Cons
          Grammarssimpexprunambig3smt2D
          (Cons
             Grammarssimpexprunambig3smt2Pl
             (Nil ::
                Grammarssimpexprunambig3smt2list
                  Grammarssimpexprunambig3smt2Tok))))
    (grammarssimpexprunambig3smt2lin b2)
grammarssimpexprunambig3smt2lin EX =
  Cons
    Grammarssimpexprunambig3smt2X
    (Nil ::
       Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok)
grammarssimpexprunambig3smt2lin EY =
  Cons
    Grammarssimpexprunambig3smt2Y
    (Nil ::
       Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok)
grammarssimpexprunambig1smt2lin ::
  Grammarssimpexprunambig3smt2E ->
    Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok
grammarssimpexprunambig1smt2lin
  (Grammarssimpexprunambig3smt2Plus a8 b3) =
  append
    (append
       (append
          (append
             (Cons
                Grammarssimpexprunambig3smt2C
                (Nil ::
                   Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok))
             (grammarssimpexprunambig1smt2lin a8))
          (Cons
             Grammarssimpexprunambig3smt2Pl
             (Nil ::
                Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok)))
       (grammarssimpexprunambig1smt2lin b3))
    (Cons
       Grammarssimpexprunambig3smt2D
       (Nil ::
          Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok))
grammarssimpexprunambig1smt2lin EX =
  Cons
    Grammarssimpexprunambig3smt2X
    (Nil ::
       Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok)
grammarssimpexprunambig1smt2lin EY =
  Cons
    Grammarssimpexprunambig3smt2Y
    (Nil ::
       Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok)
grammarssimpexprunambig2smt2lin ::
  Grammarssimpexprunambig3smt2E ->
    Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok
grammarssimpexprunambig2smt2lin
  (Grammarssimpexprunambig3smt2Plus a9 b4) =
  append
    (append
       (append
          (append
             (Cons
                Grammarssimpexprunambig3smt2C
                (Nil ::
                   Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok))
             (grammarssimpexprunambig2smt2lin a9))
          (Cons
             Grammarssimpexprunambig3smt2D
             (Cons
                Grammarssimpexprunambig3smt2Pl
                (Cons
                   Grammarssimpexprunambig3smt2C
                   (Nil ::
                      Grammarssimpexprunambig3smt2list
                        Grammarssimpexprunambig3smt2Tok)))))
       (grammarssimpexprunambig2smt2lin b4))
    (Cons
       Grammarssimpexprunambig3smt2D
       (Nil ::
          Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok))
grammarssimpexprunambig2smt2lin EX =
  Cons
    Grammarssimpexprunambig3smt2X
    (Nil ::
       Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok)
grammarssimpexprunambig2smt2lin EY =
  Cons
    Grammarssimpexprunambig3smt2Y
    (Nil ::
       Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok)
grammarssimpexprunambig5smt2linTerm ::
  Grammarssimpexprunambig5smt2T ->
    Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok
grammarssimpexprunambig5smt2linTerm TX =
  Cons
    Grammarssimpexprunambig3smt2X
    (Nil ::
       Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok)
grammarssimpexprunambig5smt2linTerm TY =
  Cons
    Grammarssimpexprunambig3smt2Y
    (Nil ::
       Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok)
grammarssimpexprunambig5smt2lin ::
  Grammarssimpexprunambig5smt2E ->
    Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok
grammarssimpexprunambig5smt2lin
  (Grammarssimpexprunambig5smt2Plus a10 b5) =
  append
    (append
       (grammarssimpexprunambig5smt2linTerm a10)
       (Cons
          Grammarssimpexprunambig3smt2Pl
          (Nil ::
             Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok)))
    (grammarssimpexprunambig5smt2lin b5)
grammarssimpexprunambig5smt2lin
  (Grammarssimpexprunambig5smt2Term t) =
  grammarssimpexprunambig5smt2linTerm t
grammarssimpexprunambig4smt2linTerm ::
  Grammarssimpexprunambig3smt2E ->
    Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok
grammarssimpexprunambig4smt2linTerm
  (Grammarssimpexprunambig3smt2Plus x z2) =
  append
    (append
       (Cons
          Grammarssimpexprunambig3smt2C
          (Nil ::
             Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok))
       (grammarssimpexprunambig4smt2lin
          (Grammarssimpexprunambig3smt2Plus x z2)))
    (Cons
       Grammarssimpexprunambig3smt2D
       (Nil ::
          Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok))
grammarssimpexprunambig4smt2linTerm EX =
  Cons
    Grammarssimpexprunambig3smt2X
    (Nil ::
       Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok)
grammarssimpexprunambig4smt2linTerm EY =
  Cons
    Grammarssimpexprunambig3smt2Y
    (Nil ::
       Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok)
grammarssimpexprunambig4smt2lin ::
  Grammarssimpexprunambig3smt2E ->
    Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok
grammarssimpexprunambig4smt2lin
  (Grammarssimpexprunambig3smt2Plus a11 b6) =
  append
    (append
       (grammarssimpexprunambig4smt2linTerm a11)
       (Cons
          Grammarssimpexprunambig3smt2Pl
          (Nil ::
             Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok)))
    (grammarssimpexprunambig4smt2linTerm b6)
grammarssimpexprunambig4smt2lin EX =
  Cons
    Grammarssimpexprunambig3smt2X
    (Nil ::
       Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok)
grammarssimpexprunambig4smt2lin EY =
  Cons
    Grammarssimpexprunambig3smt2Y
    (Nil ::
       Grammarssimpexprunambig3smt2list Grammarssimpexprunambig3smt2Tok)
linA ::
  B2 ->
    Grammarssimpexprunambig3smt2list
      GrammarspackratunambigPackratsmt2Tok
linA (GrammarspackratunambigPackratsmt2SB a12) =
  append
    (append
       (Cons
          GrammarspackratunambigPackratsmt2X
          (Nil ::
             Grammarssimpexprunambig3smt2list
               GrammarspackratunambigPackratsmt2Tok))
       (linA a12))
    (Cons
       GrammarspackratunambigPackratsmt2Y
       (Nil ::
          Grammarssimpexprunambig3smt2list
            GrammarspackratunambigPackratsmt2Tok))
linA ZB =
  Cons
    GrammarspackratunambigPackratsmt2X
    (Cons
       GrammarspackratunambigPackratsmt2Z
       (Cons
          GrammarspackratunambigPackratsmt2Y
          (Nil ::
             Grammarssimpexprunambig3smt2list
               GrammarspackratunambigPackratsmt2Tok)))
linB ::
  B2 ->
    Grammarssimpexprunambig3smt2list
      GrammarspackratunambigPackratsmt2Tok
linB (GrammarspackratunambigPackratsmt2SB b7) =
  append
    (append
       (Cons
          GrammarspackratunambigPackratsmt2X
          (Nil ::
             Grammarssimpexprunambig3smt2list
               GrammarspackratunambigPackratsmt2Tok))
       (linB b7))
    (Cons
       GrammarspackratunambigPackratsmt2Y
       (Cons
          GrammarspackratunambigPackratsmt2Y
          (Nil ::
             Grammarssimpexprunambig3smt2list
               GrammarspackratunambigPackratsmt2Tok)))
linB ZB =
  Cons
    GrammarspackratunambigPackratsmt2X
    (Cons
       GrammarspackratunambigPackratsmt2Z
       (Cons
          GrammarspackratunambigPackratsmt2Y
          (Cons
             GrammarspackratunambigPackratsmt2Y
             (Nil ::
                Grammarssimpexprunambig3smt2list
                  GrammarspackratunambigPackratsmt2Tok))))
linS ::
  GrammarspackratunambigPackratsmt2S ->
    Grammarssimpexprunambig3smt2list
      GrammarspackratunambigPackratsmt2Tok
linS (GrammarspackratunambigPackratsmt2A a13) = linA a13
linS (GrammarspackratunambigPackratsmt2B b8) = linB b8
isaplannerprop54smt2plus ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
isaplannerprop54smt2plus Isaplannerprop54smt2Z y2 = y2
isaplannerprop54smt2plus (Isaplannerprop54smt2S z3) y2 =
  Isaplannerprop54smt2S (isaplannerprop54smt2plus z3 y2)
isaplannerprop54smt2minus ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
isaplannerprop54smt2minus Isaplannerprop54smt2Z y3 =
  Isaplannerprop54smt2Z
isaplannerprop54smt2minus
  (Isaplannerprop54smt2S z4) Isaplannerprop54smt2Z =
  Isaplannerprop54smt2S z4
isaplannerprop54smt2minus
  (Isaplannerprop54smt2S z4) (Isaplannerprop54smt2S x2) =
  isaplannerprop54smt2minus z4 x2
isaplannerprop37smt2equal ::
  Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat -> P.Bool
isaplannerprop37smt2equal
  Isaplannerprop54smt2Z Isaplannerprop54smt2Z =
  P.True
isaplannerprop37smt2equal
  Isaplannerprop54smt2Z (Isaplannerprop54smt2S z5) =
  P.False
isaplannerprop37smt2equal
  (Isaplannerprop54smt2S x22) Isaplannerprop54smt2Z =
  P.False
isaplannerprop37smt2equal
  (Isaplannerprop54smt2S x22) (Isaplannerprop54smt2S y22) =
  isaplannerprop37smt2equal x22 y22
isaplannerprop37smt2elem ::
  Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat -> P.Bool
isaplannerprop37smt2elem x3 Nil = P.False
isaplannerprop37smt2elem x3 (Cons z6 ys) =
  (isaplannerprop37smt2equal x3 z6) P.||
    (isaplannerprop37smt2elem x3 ys)
isaplannerprop37smt2delete ::
  Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
      Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
isaplannerprop37smt2delete x4 Nil =
  Nil :: Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
isaplannerprop37smt2delete x4 (Cons z7 zs) =
  case isaplannerprop37smt2equal x4 z7 of
    P.True -> isaplannerprop37smt2delete x4 zs
    P.False -> Cons z7 (isaplannerprop37smt2delete x4 zs)
isaplannerprop45smt2zip ::
  Grammarssimpexprunambig3smt2list a14 ->
    Grammarssimpexprunambig3smt2list b9 ->
      Grammarssimpexprunambig3smt2list (Isaplannerprop45smt2Pair a14 b9)
isaplannerprop45smt2zip Nil y4 =
  Nil ::
    Grammarssimpexprunambig3smt2list (Isaplannerprop45smt2Pair a14 b9)
isaplannerprop45smt2zip (Cons z8 x23) Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list (Isaplannerprop45smt2Pair a14 b9)
isaplannerprop45smt2zip (Cons z8 x23) (Cons x32 x42) =
  Cons (Pair2 z8 x32) (isaplannerprop45smt2zip x23 x42)
isaplannerprop51smt2butlast ::
  Grammarssimpexprunambig3smt2list a15 ->
    Grammarssimpexprunambig3smt2list a15
isaplannerprop51smt2butlast Nil =
  Nil :: Grammarssimpexprunambig3smt2list a15
isaplannerprop51smt2butlast (Cons y5 Nil) =
  Nil :: Grammarssimpexprunambig3smt2list a15
isaplannerprop51smt2butlast (Cons y5 (Cons x24 x33)) =
  Cons y5 (isaplannerprop51smt2butlast (Cons x24 x33))
isaplannerprop64smt2last ::
  Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat
isaplannerprop64smt2last Nil = Isaplannerprop54smt2Z
isaplannerprop64smt2last (Cons y6 Nil) = y6
isaplannerprop64smt2last (Cons y6 (Cons x25 x34)) =
  isaplannerprop64smt2last (Cons x25 x34)
isaplannerprop68smt2len ::
  Grammarssimpexprunambig3smt2list a16 -> Isaplannerprop54smt2Nat
isaplannerprop68smt2len Nil = Isaplannerprop54smt2Z
isaplannerprop68smt2len (Cons y7 xs2) =
  Isaplannerprop54smt2S (isaplannerprop68smt2len xs2)
isaplannerprop68smt2le ::
  Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat -> P.Bool
isaplannerprop68smt2le Isaplannerprop54smt2Z y8 = P.True
isaplannerprop68smt2le
  (Isaplannerprop54smt2S z9) Isaplannerprop54smt2Z =
  P.False
isaplannerprop68smt2le
  (Isaplannerprop54smt2S z9) (Isaplannerprop54smt2S x26) =
  isaplannerprop68smt2le z9 x26
isaplannerprop65smt2lt ::
  Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat -> P.Bool
isaplannerprop65smt2lt x5 Isaplannerprop54smt2Z = P.False
isaplannerprop65smt2lt
  Isaplannerprop54smt2Z (Isaplannerprop54smt2S z10) =
  P.True
isaplannerprop65smt2lt
  (Isaplannerprop54smt2S x27) (Isaplannerprop54smt2S z10) =
  isaplannerprop65smt2lt x27 z10
map2 ::
  (a17 -> b10) ->
    Grammarssimpexprunambig3smt2list a17 ->
      Grammarssimpexprunambig3smt2list b10
map2 x6 Nil = Nil :: Grammarssimpexprunambig3smt2list b10
map2 x6 (Cons z11 xs3) = Cons (P.id x6 z11) (map2 x6 xs3)
isaplannerprop12smt2drop ::
  Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list a18 ->
      Grammarssimpexprunambig3smt2list a18
isaplannerprop12smt2drop Isaplannerprop54smt2Z y9 = y9
isaplannerprop12smt2drop (Isaplannerprop54smt2S z12) Nil =
  Nil :: Grammarssimpexprunambig3smt2list a18
isaplannerprop12smt2drop
  (Isaplannerprop54smt2S z12) (Cons x28 x35) =
  isaplannerprop12smt2drop z12 x35
max2 ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
max2 Isaplannerprop54smt2Z y10 = y10
max2 (Isaplannerprop54smt2S z13) Isaplannerprop54smt2Z =
  Isaplannerprop54smt2S z13
max2 (Isaplannerprop54smt2S z13) (Isaplannerprop54smt2S x29) =
  Isaplannerprop54smt2S (max2 z13 x29)
isaplannerprop71smt2ins ::
  Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
      Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
isaplannerprop71smt2ins x7 Nil =
  Cons
    x7
    (Nil :: Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat)
isaplannerprop71smt2ins x7 (Cons z14 xs4) =
  case isaplannerprop65smt2lt x7 z14 of
    P.True -> Cons x7 (Cons z14 xs4)
    P.False -> Cons z14 (isaplannerprop71smt2ins x7 xs4)
isaplannerprop05smt2count ::
  Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
      Isaplannerprop54smt2Nat
isaplannerprop05smt2count x8 Nil = Isaplannerprop54smt2Z
isaplannerprop05smt2count x8 (Cons z15 ys2) =
  case isaplannerprop37smt2equal x8 z15 of
    P.True -> Isaplannerprop54smt2S (isaplannerprop05smt2count x8 ys2)
    P.False -> isaplannerprop05smt2count x8 ys2
isaplannerprop85smt2rev ::
  Grammarssimpexprunambig3smt2list a19 ->
    Grammarssimpexprunambig3smt2list a19
isaplannerprop85smt2rev Nil =
  Nil :: Grammarssimpexprunambig3smt2list a19
isaplannerprop85smt2rev (Cons y11 xs5) =
  append
    (isaplannerprop85smt2rev xs5)
    (Cons y11 (Nil :: Grammarssimpexprunambig3smt2list a19))
dropWhile ::
  (a20 -> P.Bool) ->
    Grammarssimpexprunambig3smt2list a20 ->
      Grammarssimpexprunambig3smt2list a20
dropWhile x9 Nil = Nil :: Grammarssimpexprunambig3smt2list a20
dropWhile x9 (Cons z16 xs6) =
  case P.id x9 z16 of
    P.True -> dropWhile x9 xs6
    P.False -> Cons z16 xs6
isaplannerprop82smt2take ::
  Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list a21 ->
      Grammarssimpexprunambig3smt2list a21
isaplannerprop82smt2take Isaplannerprop54smt2Z y12 =
  Nil :: Grammarssimpexprunambig3smt2list a21
isaplannerprop82smt2take (Isaplannerprop54smt2S z17) Nil =
  Nil :: Grammarssimpexprunambig3smt2list a21
isaplannerprop82smt2take
  (Isaplannerprop54smt2S z17) (Cons x210 x36) =
  Cons x210 (isaplannerprop82smt2take z17 x36)
null :: Grammarssimpexprunambig3smt2list a22 -> P.Bool
null Nil = P.True
null (Cons y13 z18) = P.False
ins1 ::
  Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
      Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
ins1 x10 Nil =
  Cons
    x10
    (Nil :: Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat)
ins1 x10 (Cons z19 xs7) =
  case isaplannerprop37smt2equal x10 z19 of
    P.True -> Cons z19 xs7
    P.False -> Cons z19 (ins1 x10 xs7)
takeWhile ::
  (a23 -> P.Bool) ->
    Grammarssimpexprunambig3smt2list a23 ->
      Grammarssimpexprunambig3smt2list a23
takeWhile x11 Nil = Nil :: Grammarssimpexprunambig3smt2list a23
takeWhile x11 (Cons z20 xs8) =
  case P.id x11 z20 of
    P.True -> Cons z20 (takeWhile x11 xs8)
    P.False -> Nil :: Grammarssimpexprunambig3smt2list a23
min2 ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
min2 Isaplannerprop54smt2Z y14 = Isaplannerprop54smt2Z
min2 (Isaplannerprop54smt2S z21) Isaplannerprop54smt2Z =
  Isaplannerprop54smt2Z
min2 (Isaplannerprop54smt2S z21) (Isaplannerprop54smt2S y23) =
  Isaplannerprop54smt2S (min2 z21 y23)
insort ::
  Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
      Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
insort x12 Nil =
  Cons
    x12
    (Nil :: Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat)
insort x12 (Cons z22 xs9) =
  case isaplannerprop68smt2le x12 z22 of
    P.True -> Cons x12 (Cons z22 xs9)
    P.False -> Cons z22 (insort x12 xs9)
isaplannerprop53smt2sort ::
  Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
isaplannerprop53smt2sort Nil =
  Nil :: Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
isaplannerprop53smt2sort (Cons y15 xs10) =
  insort y15 (isaplannerprop53smt2sort xs10)
isaplannerprop78smt2sorted ::
  Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat -> P.Bool
isaplannerprop78smt2sorted Nil = P.True
isaplannerprop78smt2sorted (Cons y16 Nil) = P.True
isaplannerprop78smt2sorted (Cons y16 (Cons y24 ys3)) =
  (isaplannerprop68smt2le y16 y24) P.&&
    (isaplannerprop78smt2sorted (Cons y24 ys3))
filter ::
  (a24 -> P.Bool) ->
    Grammarssimpexprunambig3smt2list a24 ->
      Grammarssimpexprunambig3smt2list a24
filter x13 Nil = Nil :: Grammarssimpexprunambig3smt2list a24
filter x13 (Cons z23 xs11) =
  case P.id x13 z23 of
    P.True -> Cons z23 (filter x13 xs11)
    P.False -> filter x13 xs11
zipConcat ::
  a25 ->
    Grammarssimpexprunambig3smt2list a25 ->
      Grammarssimpexprunambig3smt2list b11 ->
        Grammarssimpexprunambig3smt2list (Isaplannerprop45smt2Pair a25 b11)
zipConcat x14 y17 Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list (Isaplannerprop45smt2Pair a25 b11)
zipConcat x14 y17 (Cons y25 ys4) =
  Cons (Pair2 x14 y25) (isaplannerprop45smt2zip y17 ys4)
mirror ::
  Isaplannerprop47smt2Tree a26 -> Isaplannerprop47smt2Tree a26
mirror Leaf = Leaf :: Isaplannerprop47smt2Tree a26
mirror (Isaplannerprop47smt2Node l y18 r) =
  Isaplannerprop47smt2Node (mirror r) y18 (mirror l)
height :: Isaplannerprop47smt2Tree a27 -> Isaplannerprop54smt2Nat
height Leaf = Isaplannerprop54smt2Z
height (Isaplannerprop47smt2Node l2 y19 p) =
  Isaplannerprop54smt2S (max2 (height l2) (height p))
lastOfTwo ::
  Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
      Isaplannerprop54smt2Nat
lastOfTwo x15 Nil = isaplannerprop64smt2last x15
lastOfTwo x15 (Cons z24 x211) =
  isaplannerprop64smt2last (Cons z24 x211)
butlastConcat ::
  Grammarssimpexprunambig3smt2list a28 ->
    Grammarssimpexprunambig3smt2list a28 ->
      Grammarssimpexprunambig3smt2list a28
butlastConcat x16 Nil = isaplannerprop51smt2butlast x16
butlastConcat x16 (Cons z25 x212) =
  append x16 (isaplannerprop51smt2butlast (Cons z25 x212))
go ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat ->
      Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
go x17 y20 Isaplannerprop54smt2Z = Isaplannerprop54smt2Z
go
  Isaplannerprop54smt2Z Isaplannerprop54smt2Z
  (Isaplannerprop54smt2S x213) =
  Isaplannerprop54smt2Z
go
  Isaplannerprop54smt2Z (Isaplannerprop54smt2S n)
  (Isaplannerprop54smt2S x213) =
  isaplannerprop54smt2minus
    (Isaplannerprop54smt2S x213) (Isaplannerprop54smt2S n)
go
  (Isaplannerprop54smt2S m) Isaplannerprop54smt2Z
  (Isaplannerprop54smt2S x213) =
  go m x213 (Isaplannerprop54smt2S x213)
go
  (Isaplannerprop54smt2S m) (Isaplannerprop54smt2S k)
  (Isaplannerprop54smt2S x213) =
  go m k (Isaplannerprop54smt2S x213)
modstructural ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
modstructural x18 y21 = go x18 Isaplannerprop54smt2Z y21
tip2015rotatestructuralmodsmt2rotate ::
  Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list a29 ->
      Grammarssimpexprunambig3smt2list a29
tip2015rotatestructuralmodsmt2rotate Isaplannerprop54smt2Z y26 =
  y26
tip2015rotatestructuralmodsmt2rotate
  (Isaplannerprop54smt2S z26) Nil =
  Nil :: Grammarssimpexprunambig3smt2list a29
tip2015rotatestructuralmodsmt2rotate
  (Isaplannerprop54smt2S z26) (Cons x214 x37) =
  tip2015rotatestructuralmodsmt2rotate
    z26
    (append
       x37 (Cons x214 (Nil :: Grammarssimpexprunambig3smt2list a29)))
tip2015intaddassocsmt2minus ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat -> Tip2015intaddassocsmt2Integer
tip2015intaddassocsmt2minus
  Isaplannerprop54smt2Z Isaplannerprop54smt2Z =
  Tip2015intaddassocsmt2P Isaplannerprop54smt2Z
tip2015intaddassocsmt2minus
  Isaplannerprop54smt2Z (Isaplannerprop54smt2S o) =
  Tip2015intaddassocsmt2N o
tip2015intaddassocsmt2minus
  (Isaplannerprop54smt2S m2) Isaplannerprop54smt2Z =
  Tip2015intaddassocsmt2P (Isaplannerprop54smt2S m2)
tip2015intaddassocsmt2minus
  (Isaplannerprop54smt2S m2) (Isaplannerprop54smt2S o2) =
  tip2015intaddassocsmt2minus m2 o2
tip2015intaddassocsmt2plus ::
  Tip2015intaddassocsmt2Integer ->
    Tip2015intaddassocsmt2Integer -> Tip2015intaddassocsmt2Integer
tip2015intaddassocsmt2plus
  (Tip2015intaddassocsmt2P m3) (Tip2015intaddassocsmt2P n2) =
  Tip2015intaddassocsmt2P (isaplannerprop54smt2plus m3 n2)
tip2015intaddassocsmt2plus
  (Tip2015intaddassocsmt2P m3) (Tip2015intaddassocsmt2N o3) =
  tip2015intaddassocsmt2minus m3 (Isaplannerprop54smt2S o3)
tip2015intaddassocsmt2plus
  (Tip2015intaddassocsmt2N m22) (Tip2015intaddassocsmt2P n22) =
  tip2015intaddassocsmt2minus n22 (Isaplannerprop54smt2S m22)
tip2015intaddassocsmt2plus
  (Tip2015intaddassocsmt2N m22) (Tip2015intaddassocsmt2N n3) =
  Tip2015intaddassocsmt2N
    (Isaplannerprop54smt2S (isaplannerprop54smt2plus m22 n3))
tip2015weirdnatadd3comm12smt2add3 ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat ->
      Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
tip2015weirdnatadd3comm12smt2add3
  Isaplannerprop54smt2Z Isaplannerprop54smt2Z z27 =
  z27
tip2015weirdnatadd3comm12smt2add3
  Isaplannerprop54smt2Z (Isaplannerprop54smt2S y27) z27 =
  Isaplannerprop54smt2S
    (tip2015weirdnatadd3comm12smt2add3 Isaplannerprop54smt2Z y27 z27)
tip2015weirdnatadd3comm12smt2add3
  (Isaplannerprop54smt2S x215) y28 z27 =
  Isaplannerprop54smt2S
    (tip2015weirdnatadd3comm12smt2add3 x215 y28 z27)
tip2015weirdnatmul3assoc2smt2mul3 ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat ->
      Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
tip2015weirdnatmul3assoc2smt2mul3 Isaplannerprop54smt2Z y29 z28 =
  Isaplannerprop54smt2Z
tip2015weirdnatmul3assoc2smt2mul3
  (Isaplannerprop54smt2S x216) Isaplannerprop54smt2Z z28 =
  Isaplannerprop54smt2Z
tip2015weirdnatmul3assoc2smt2mul3
  (Isaplannerprop54smt2S x216) (Isaplannerprop54smt2S x38)
  Isaplannerprop54smt2Z =
  Isaplannerprop54smt2Z
tip2015weirdnatmul3assoc2smt2mul3
  (Isaplannerprop54smt2S Isaplannerprop54smt2Z)
  (Isaplannerprop54smt2S Isaplannerprop54smt2Z)
  (Isaplannerprop54smt2S Isaplannerprop54smt2Z) =
  Isaplannerprop54smt2S Isaplannerprop54smt2Z
tip2015weirdnatmul3assoc2smt2mul3
  (Isaplannerprop54smt2S Isaplannerprop54smt2Z)
  (Isaplannerprop54smt2S Isaplannerprop54smt2Z)
  (Isaplannerprop54smt2S (Isaplannerprop54smt2S x52)) =
  Isaplannerprop54smt2S
    (tip2015weirdnatadd3comm12smt2add3
       (tip2015weirdnatmul3assoc2smt2mul3
          Isaplannerprop54smt2Z Isaplannerprop54smt2Z
          (Isaplannerprop54smt2S x52))
       (tip2015weirdnatadd3comm12smt2add3
          (tip2015weirdnatmul3assoc2smt2mul3
             (Isaplannerprop54smt2S Isaplannerprop54smt2Z) Isaplannerprop54smt2Z
             (Isaplannerprop54smt2S x52))
          (tip2015weirdnatmul3assoc2smt2mul3
             Isaplannerprop54smt2Z (Isaplannerprop54smt2S Isaplannerprop54smt2Z)
             (Isaplannerprop54smt2S x52))
          (tip2015weirdnatmul3assoc2smt2mul3
             Isaplannerprop54smt2Z Isaplannerprop54smt2Z
             (Isaplannerprop54smt2S Isaplannerprop54smt2Z)))
       (tip2015weirdnatadd3comm12smt2add3
          Isaplannerprop54smt2Z Isaplannerprop54smt2Z
          (Isaplannerprop54smt2S x52)))
tip2015weirdnatmul3assoc2smt2mul3
  (Isaplannerprop54smt2S Isaplannerprop54smt2Z)
  (Isaplannerprop54smt2S (Isaplannerprop54smt2S x62))
  (Isaplannerprop54smt2S x43) =
  Isaplannerprop54smt2S
    (tip2015weirdnatadd3comm12smt2add3
       (tip2015weirdnatmul3assoc2smt2mul3
          Isaplannerprop54smt2Z (Isaplannerprop54smt2S x62) x43)
       (tip2015weirdnatadd3comm12smt2add3
          (tip2015weirdnatmul3assoc2smt2mul3
             (Isaplannerprop54smt2S Isaplannerprop54smt2Z)
             (Isaplannerprop54smt2S x62) x43)
          (tip2015weirdnatmul3assoc2smt2mul3
             Isaplannerprop54smt2Z (Isaplannerprop54smt2S Isaplannerprop54smt2Z)
             x43)
          (tip2015weirdnatmul3assoc2smt2mul3
             Isaplannerprop54smt2Z (Isaplannerprop54smt2S x62)
             (Isaplannerprop54smt2S Isaplannerprop54smt2Z)))
       (tip2015weirdnatadd3comm12smt2add3
          Isaplannerprop54smt2Z (Isaplannerprop54smt2S x62) x43))
tip2015weirdnatmul3assoc2smt2mul3
  (Isaplannerprop54smt2S (Isaplannerprop54smt2S x72))
  (Isaplannerprop54smt2S x38) (Isaplannerprop54smt2S x43) =
  Isaplannerprop54smt2S
    (tip2015weirdnatadd3comm12smt2add3
       (tip2015weirdnatmul3assoc2smt2mul3
          (Isaplannerprop54smt2S x72) x38 x43)
       (tip2015weirdnatadd3comm12smt2add3
          (tip2015weirdnatmul3assoc2smt2mul3
             (Isaplannerprop54smt2S Isaplannerprop54smt2Z) x38 x43)
          (tip2015weirdnatmul3assoc2smt2mul3
             (Isaplannerprop54smt2S x72)
             (Isaplannerprop54smt2S Isaplannerprop54smt2Z) x43)
          (tip2015weirdnatmul3assoc2smt2mul3
             (Isaplannerprop54smt2S x72) x38
             (Isaplannerprop54smt2S Isaplannerprop54smt2Z)))
       (tip2015weirdnatadd3comm12smt2add3
          (Isaplannerprop54smt2S x72) x38 x43))
accplus ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
accplus Isaplannerprop54smt2Z y30 = y30
accplus (Isaplannerprop54smt2S z29) y30 =
  accplus z29 (Isaplannerprop54smt2S y30)
tip2015nataccaltmulcommsmt2accaltmul ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
tip2015nataccaltmulcommsmt2accaltmul Isaplannerprop54smt2Z y31 =
  Isaplannerprop54smt2Z
tip2015nataccaltmulcommsmt2accaltmul
  (Isaplannerprop54smt2S z30) Isaplannerprop54smt2Z =
  Isaplannerprop54smt2Z
tip2015nataccaltmulcommsmt2accaltmul
  (Isaplannerprop54smt2S z30) (Isaplannerprop54smt2S x217) =
  Isaplannerprop54smt2S
    (accplus
       z30 (accplus x217 (tip2015nataccaltmulcommsmt2accaltmul z30 x217)))
tip2015listzpermtranssmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015listzpermtranssmt2zelem x19 Nil = P.False
tip2015listzpermtranssmt2zelem x19 (Cons z31 ys5) =
  (x19 P.== z31) P.|| (tip2015listzpermtranssmt2zelem x19 ys5)
tip2015listzpermtranssmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015listzpermtranssmt2zdelete x20 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015listzpermtranssmt2zdelete x20 (Cons z32 ys6) =
  case x20 P.== z32 of
    P.True -> ys6
    P.False -> Cons z32 (tip2015listzpermtranssmt2zdelete x20 ys6)
tip2015listzpermtranssmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015listzpermtranssmt2zisPermutation Nil y32 = null y32
tip2015listzpermtranssmt2zisPermutation (Cons z33 xs12) y32 =
  (tip2015listzpermtranssmt2zelem z33 y32) P.&&
    (tip2015listzpermtranssmt2zisPermutation
       xs12 (tip2015listzpermtranssmt2zdelete z33 y32))
tip2015sortMSortBU2Sortssmt2zisaplannerprop78smt2sorted ::
  Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortMSortBU2Sortssmt2zisaplannerprop78smt2sorted Nil =
  P.True
tip2015sortMSortBU2Sortssmt2zisaplannerprop78smt2sorted
  (Cons y33 Nil) =
  P.True
tip2015sortMSortBU2Sortssmt2zisaplannerprop78smt2sorted
  (Cons y33 (Cons y210 xs13)) =
  (y33 P.<= y210) P.&&
    (tip2015sortMSortBU2Sortssmt2zisaplannerprop78smt2sorted
       (Cons y210 xs13))
tip2015sortMSortBU2Sortssmt2risers ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBU2Sortssmt2risers Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBU2Sortssmt2risers (Cons y34 Nil) =
  Cons
    (Cons y34 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Grammarssimpexprunambig3smt2list P.Int))
tip2015sortMSortBU2Sortssmt2risers (Cons y34 (Cons y211 xs14)) =
  case y34 P.<= y211 of
    P.True ->
      case tip2015sortMSortBU2Sortssmt2risers (Cons y211 xs14) of
        Nil ->
          Nil ::
            Grammarssimpexprunambig3smt2list
              (Grammarssimpexprunambig3smt2list P.Int)
        Cons ys7 yss -> Cons (Cons y34 ys7) yss
    P.False ->
      Cons
        (Cons y34 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
        (tip2015sortMSortBU2Sortssmt2risers (Cons y211 xs14))
tip2015sortMSortBU2Sortssmt2lmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2Sortssmt2lmerge Nil y35 = y35
tip2015sortMSortBU2Sortssmt2lmerge (Cons z34 x218) Nil =
  Cons z34 x218
tip2015sortMSortBU2Sortssmt2lmerge (Cons z34 x218) (Cons x39 x44) =
  case z34 P.<= x39 of
    P.True ->
      Cons z34 (tip2015sortMSortBU2Sortssmt2lmerge x218 (Cons x39 x44))
    P.False ->
      Cons x39 (tip2015sortMSortBU2Sortssmt2lmerge (Cons z34 x218) x44)
tip2015sortMSortBU2Sortssmt2pairwise ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list P.Int) ->
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBU2Sortssmt2pairwise Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBU2Sortssmt2pairwise (Cons xs15 Nil) =
  Cons
    xs15
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Grammarssimpexprunambig3smt2list P.Int))
tip2015sortMSortBU2Sortssmt2pairwise (Cons xs15 (Cons ys8 xss)) =
  Cons
    (tip2015sortMSortBU2Sortssmt2lmerge xs15 ys8)
    (tip2015sortMSortBU2Sortssmt2pairwise xss)
tip2015sortMSortBU2Sortssmt2mergingbu2 ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list P.Int) ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2Sortssmt2mergingbu2 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2Sortssmt2mergingbu2 (Cons xs16 Nil) = xs16
tip2015sortMSortBU2Sortssmt2mergingbu2
  (Cons xs16 (Cons z35 x219)) =
  tip2015sortMSortBU2Sortssmt2mergingbu2
    (tip2015sortMSortBU2Sortssmt2pairwise (Cons xs16 (Cons z35 x219)))
tip2015sortMSortBU2Sortssmt2msortbu2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2Sortssmt2msortbu2 x21 =
  tip2015sortMSortBU2Sortssmt2mergingbu2
    (tip2015sortMSortBU2Sortssmt2risers x21)
tip2015regexpRecPlussmt2seq ::
  Tip2015regexpRecPlussmt2R ->
    Tip2015regexpRecPlussmt2R -> Tip2015regexpRecPlussmt2R
tip2015regexpRecPlussmt2seq x30 y36 =
  case x30 of
    Tip2015regexpRecPlussmt2Nil -> Tip2015regexpRecPlussmt2Nil
    _ ->
      case y36 of
        Tip2015regexpRecPlussmt2Nil -> Tip2015regexpRecPlussmt2Nil
        _ ->
          case x30 of
            Eps -> y36
            _ ->
              case y36 of
                Eps -> x30
                _ -> Tip2015regexpRecPlussmt2Seq x30 y36
tip2015regexpRecPlussmt2plus ::
  Tip2015regexpRecPlussmt2R ->
    Tip2015regexpRecPlussmt2R -> Tip2015regexpRecPlussmt2R
tip2015regexpRecPlussmt2plus x31 y37 =
  case x31 of
    Tip2015regexpRecPlussmt2Nil -> y37
    _ ->
      case y37 of
        Tip2015regexpRecPlussmt2Nil -> x31
        _ -> Tip2015regexpRecPlussmt2Plus x31 y37
eqA ::
  Grammarssimpexprunambig5smt2T ->
    Grammarssimpexprunambig5smt2T -> P.Bool
eqA TX TX = P.True
eqA TX TY = P.False
eqA TY TX = P.False
eqA TY TY = P.True
tip2015regexpRecPlussmt2eps :: Tip2015regexpRecPlussmt2R -> P.Bool
tip2015regexpRecPlussmt2eps x40 =
  case x40 of
    Eps -> P.True
    Tip2015regexpRecPlussmt2Plus q q2 ->
      (tip2015regexpRecPlussmt2eps q) P.||
        (tip2015regexpRecPlussmt2eps q2)
    Tip2015regexpRecPlussmt2Seq p2 q22 ->
      (tip2015regexpRecPlussmt2eps p2) P.&&
        (tip2015regexpRecPlussmt2eps q22)
    Tip2015regexpRecPlussmt2Star y38 -> P.True
    _ -> P.False
epsR :: Tip2015regexpRecPlussmt2R -> Tip2015regexpRecPlussmt2R
epsR x41 =
  case tip2015regexpRecPlussmt2eps x41 of
    P.True -> Eps
    P.False -> Tip2015regexpRecPlussmt2Nil
step ::
  Tip2015regexpRecPlussmt2R ->
    Grammarssimpexprunambig5smt2T -> Tip2015regexpRecPlussmt2R
step x45 y39 =
  case x45 of
    Tip2015regexpRecPlussmt2Atom a30 ->
      case eqA a30 y39 of
        P.True -> Eps
        P.False -> Tip2015regexpRecPlussmt2Nil
    Tip2015regexpRecPlussmt2Plus p3 q3 ->
      tip2015regexpRecPlussmt2plus (step p3 y39) (step q3 y39)
    Tip2015regexpRecPlussmt2Seq p22 q23 ->
      tip2015regexpRecPlussmt2plus
        (tip2015regexpRecPlussmt2seq (step p22 y39) q23)
        (tip2015regexpRecPlussmt2seq (epsR p22) (step q23 y39))
    Tip2015regexpRecPlussmt2Star p32 ->
      tip2015regexpRecPlussmt2seq (step p32 y39) x45
    _ -> Tip2015regexpRecPlussmt2Nil
recognise ::
  Tip2015regexpRecPlussmt2R ->
    Grammarssimpexprunambig3smt2list Grammarssimpexprunambig5smt2T ->
      P.Bool
recognise x46 Nil = tip2015regexpRecPlussmt2eps x46
recognise x46 (Cons z36 xs17) = recognise (step x46 z36) xs17
tip2015listconcatmapbindsmt2bind ::
  Grammarssimpexprunambig3smt2list a31 ->
    (a31 -> Grammarssimpexprunambig3smt2list b12) ->
      Grammarssimpexprunambig3smt2list b12
tip2015listconcatmapbindsmt2bind Nil y40 =
  Nil :: Grammarssimpexprunambig3smt2list b12
tip2015listconcatmapbindsmt2bind (Cons z37 xs18) y40 =
  append (P.id y40 z37) (tip2015listconcatmapbindsmt2bind xs18 y40)
concat2 ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list a32) ->
    Grammarssimpexprunambig3smt2list a32
concat2 Nil = Nil :: Grammarssimpexprunambig3smt2list a32
concat2 (Cons xs19 zss) = append xs19 (concat2 zss)
add3acc ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat ->
      Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
add3acc Isaplannerprop54smt2Z Isaplannerprop54smt2Z z38 = z38
add3acc Isaplannerprop54smt2Z (Isaplannerprop54smt2S y212) z38 =
  add3acc Isaplannerprop54smt2Z y212 (Isaplannerprop54smt2S z38)
add3acc (Isaplannerprop54smt2S x220) y41 z38 =
  add3acc x220 (Isaplannerprop54smt2S y41) z38
tip2015nataltmulsamesmt2mult ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
tip2015nataltmulsamesmt2mult Isaplannerprop54smt2Z y42 =
  Isaplannerprop54smt2Z
tip2015nataltmulsamesmt2mult (Isaplannerprop54smt2S n4) y42 =
  isaplannerprop54smt2plus y42 (tip2015nataltmulsamesmt2mult n4 y42)
tip2015nataltmulsamesmt2altmul ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
tip2015nataltmulsamesmt2altmul Isaplannerprop54smt2Z y43 =
  Isaplannerprop54smt2Z
tip2015nataltmulsamesmt2altmul
  (Isaplannerprop54smt2S z39) Isaplannerprop54smt2Z =
  Isaplannerprop54smt2Z
tip2015nataltmulsamesmt2altmul
  (Isaplannerprop54smt2S z39) (Isaplannerprop54smt2S x221) =
  Isaplannerprop54smt2S
    (isaplannerprop54smt2plus
       (isaplannerprop54smt2plus
          (tip2015nataltmulsamesmt2altmul z39 x221) z39)
       x221)
fst :: Isaplannerprop45smt2Pair a33 b13 -> a33
fst (Pair2 y44 z40) = y44
tip2015sortMSortTDSortssmt2ztake ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a34 ->
      Grammarssimpexprunambig3smt2list a34
tip2015sortMSortTDSortssmt2ztake x47 y45 =
  case x47 P.== (0) of
    P.True -> Nil :: Grammarssimpexprunambig3smt2list a34
    P.False ->
      case y45 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a34
        Cons z41 xs20 ->
          Cons z41 (tip2015sortMSortTDSortssmt2ztake (x47 P.- (1)) xs20)
tip2015sortMSortTDSortssmt2zisaplannerprop78smt2sorted ::
  Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortMSortTDSortssmt2zisaplannerprop78smt2sorted Nil = P.True
tip2015sortMSortTDSortssmt2zisaplannerprop78smt2sorted
  (Cons y46 Nil) =
  P.True
tip2015sortMSortTDSortssmt2zisaplannerprop78smt2sorted
  (Cons y46 (Cons y213 xs21)) =
  (y46 P.<= y213) P.&&
    (tip2015sortMSortTDSortssmt2zisaplannerprop78smt2sorted
       (Cons y213 xs21))
tip2015sortMSortTDSortssmt2zlength ::
  Grammarssimpexprunambig3smt2list a35 -> P.Int
tip2015sortMSortTDSortssmt2zlength Nil = 0
tip2015sortMSortTDSortssmt2zlength (Cons y47 xs22) =
  (1) P.+ (tip2015sortMSortTDSortssmt2zlength xs22)
tip2015sortMSortTDSortssmt2zdrop ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a36 ->
      Grammarssimpexprunambig3smt2list a36
tip2015sortMSortTDSortssmt2zdrop x48 y48 =
  case x48 P.== (0) of
    P.True -> y48
    P.False ->
      case y48 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a36
        Cons z42 xs1 -> tip2015sortMSortTDSortssmt2zdrop (x48 P.- (1)) xs1
tip2015sortMSortTDSortssmt2lmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortTDSortssmt2lmerge Nil y49 = y49
tip2015sortMSortTDSortssmt2lmerge (Cons z43 x222) Nil =
  Cons z43 x222
tip2015sortMSortTDSortssmt2lmerge (Cons z43 x222) (Cons x310 x49) =
  case z43 P.<= x310 of
    P.True ->
      Cons z43 (tip2015sortMSortTDSortssmt2lmerge x222 (Cons x310 x49))
    P.False ->
      Cons x310 (tip2015sortMSortTDSortssmt2lmerge (Cons z43 x222) x49)
tip2015sortMSortTDSortssmt2msorttd ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortTDSortssmt2msorttd Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortTDSortssmt2msorttd (Cons y50 Nil) =
  Cons y50 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortTDSortssmt2msorttd (Cons y50 (Cons x223 x311)) =
  let i =
        P.div
          (tip2015sortMSortTDSortssmt2zlength (Cons y50 (Cons x223 x311)))
          (2)
    in tip2015sortMSortTDSortssmt2lmerge
         (tip2015sortMSortTDSortssmt2msorttd
            (tip2015sortMSortTDSortssmt2ztake i (Cons y50 (Cons x223 x311))))
         (tip2015sortMSortTDSortssmt2msorttd
            (tip2015sortMSortTDSortssmt2zdrop i (Cons y50 (Cons x223 x311))))
tip2015listpermelemsmt2delete ::
  Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
      Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
tip2015listpermelemsmt2delete x50 Nil =
  Nil :: Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
tip2015listpermelemsmt2delete x50 (Cons z44 xs23) =
  case isaplannerprop37smt2equal x50 z44 of
    P.True -> xs23
    P.False -> Cons z44 (tip2015listpermelemsmt2delete x50 xs23)
tip2015listpermelemsmt2isPermutation ::
  Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat -> P.Bool
tip2015listpermelemsmt2isPermutation Nil y51 = null y51
tip2015listpermelemsmt2isPermutation (Cons z45 xs24) y51 =
  (isaplannerprop37smt2elem z45 y51) P.&&
    (tip2015listpermelemsmt2isPermutation
       xs24 (tip2015listpermelemsmt2delete z45 y51))
tip2015sortMSortBUCountsmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015sortMSortBUCountsmt2zcount x51 Nil = Isaplannerprop54smt2Z
tip2015sortMSortBUCountsmt2zcount x51 (Cons z46 xs25) =
  case x51 P.== z46 of
    P.True ->
      Isaplannerprop54smt2S (tip2015sortMSortBUCountsmt2zcount x51 xs25)
    P.False -> tip2015sortMSortBUCountsmt2zcount x51 xs25
tip2015sortMSortBUCountsmt2lmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUCountsmt2lmerge Nil y52 = y52
tip2015sortMSortBUCountsmt2lmerge (Cons z47 x224) Nil =
  Cons z47 x224
tip2015sortMSortBUCountsmt2lmerge
  (Cons z47 x224) (Cons x312 x410) =
  case z47 P.<= x312 of
    P.True ->
      Cons z47 (tip2015sortMSortBUCountsmt2lmerge x224 (Cons x312 x410))
    P.False ->
      Cons x312 (tip2015sortMSortBUCountsmt2lmerge (Cons z47 x224) x410)
tip2015sortMSortBUCountsmt2pairwise ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list P.Int) ->
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBUCountsmt2pairwise Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBUCountsmt2pairwise (Cons xs26 Nil) =
  Cons
    xs26
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Grammarssimpexprunambig3smt2list P.Int))
tip2015sortMSortBUCountsmt2pairwise (Cons xs26 (Cons ys9 xss2)) =
  Cons
    (tip2015sortMSortBUCountsmt2lmerge xs26 ys9)
    (tip2015sortMSortBUCountsmt2pairwise xss2)
tip2015sortMSortBUCountsmt2mergingbu ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list P.Int) ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUCountsmt2mergingbu Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUCountsmt2mergingbu (Cons xs27 Nil) = xs27
tip2015sortMSortBUCountsmt2mergingbu (Cons xs27 (Cons z48 x225)) =
  tip2015sortMSortBUCountsmt2mergingbu
    (tip2015sortMSortBUCountsmt2pairwise (Cons xs27 (Cons z48 x225)))
tip2015sortMSortBUCountsmt2msortbu ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUCountsmt2msortbu x53 =
  tip2015sortMSortBUCountsmt2mergingbu
    (map2
       (\ y53 -> Cons y53 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
       x53)
(^) :: Isaplannerprop54smt2Nat
(^) = Isaplannerprop54smt2S Isaplannerprop54smt2Z
tip2015natpowonesmt2pow ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
tip2015natpowonesmt2pow x54 Isaplannerprop54smt2Z = (^)
tip2015natpowonesmt2pow x54 (Isaplannerprop54smt2S m4) =
  tip2015nataltmulsamesmt2mult x54 (tip2015natpowonesmt2pow x54 m4)
tip2015treesortAddSamesmt2flatten ::
  Tip2015treesortAddSamesmt2Tree a37 ->
    Grammarssimpexprunambig3smt2list a37 ->
      Grammarssimpexprunambig3smt2list a37
tip2015treesortAddSamesmt2flatten
  (Tip2015treesortAddSamesmt2Node q4 z49 q24) y54 =
  tip2015treesortAddSamesmt2flatten
    q4 (Cons z49 (tip2015treesortAddSamesmt2flatten q24 y54))
tip2015treesortAddSamesmt2flatten
  Tip2015treesortAddSamesmt2Nil y54 =
  y54
tip2015treesortAddSamesmt2add ::
  Isaplannerprop54smt2Nat ->
    Tip2015treesortAddSamesmt2Tree Isaplannerprop54smt2Nat ->
      Tip2015treesortAddSamesmt2Tree Isaplannerprop54smt2Nat
tip2015treesortAddSamesmt2add
  x55 (Tip2015treesortAddSamesmt2Node q5 z50 q25) =
  case isaplannerprop68smt2le x55 z50 of
    P.True ->
      Tip2015treesortAddSamesmt2Node
        (tip2015treesortAddSamesmt2add x55 q5) z50 q25
    P.False ->
      Tip2015treesortAddSamesmt2Node
        q5 z50 (tip2015treesortAddSamesmt2add x55 q25)
tip2015treesortAddSamesmt2add x55 Tip2015treesortAddSamesmt2Nil =
  Tip2015treesortAddSamesmt2Node
    (Tip2015treesortAddSamesmt2Nil ::
       Tip2015treesortAddSamesmt2Tree Isaplannerprop54smt2Nat)
    x55
    (Tip2015treesortAddSamesmt2Nil ::
       Tip2015treesortAddSamesmt2Tree Isaplannerprop54smt2Nat)
tip2015heapSortPermutessmt2merge ::
  Tip2015heapSortPermutessmt2Heap ->
    Tip2015heapSortPermutessmt2Heap -> Tip2015heapSortPermutessmt2Heap
tip2015heapSortPermutessmt2merge
  (Tip2015heapSortPermutessmt2Node z51 x226 x313)
  (Tip2015heapSortPermutessmt2Node x411 x56 x63) =
  case isaplannerprop68smt2le x226 x56 of
    P.True ->
      Tip2015heapSortPermutessmt2Node
        (tip2015heapSortPermutessmt2merge
           x313 (Tip2015heapSortPermutessmt2Node x411 x56 x63))
        x226 z51
    P.False ->
      Tip2015heapSortPermutessmt2Node
        (tip2015heapSortPermutessmt2merge
           (Tip2015heapSortPermutessmt2Node z51 x226 x313) x63)
        x56 x411
tip2015heapSortPermutessmt2merge
  (Tip2015heapSortPermutessmt2Node z51 x226 x313)
  Tip2015heapSortPermutessmt2Nil =
  Tip2015heapSortPermutessmt2Node z51 x226 x313
tip2015heapSortPermutessmt2merge
  Tip2015heapSortPermutessmt2Nil y55 =
  y55
tip2015heapSortPermutessmt2toList ::
  Isaplannerprop54smt2Nat ->
    Tip2015heapSortPermutessmt2Heap ->
      Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
tip2015heapSortPermutessmt2toList Isaplannerprop54smt2Z y56 =
  Nil :: Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
tip2015heapSortPermutessmt2toList
  (Isaplannerprop54smt2S z52)
  (Tip2015heapSortPermutessmt2Node x227 x314 x412) =
  Cons
    x314
    (tip2015heapSortPermutessmt2toList
       z52 (tip2015heapSortPermutessmt2merge x227 x412))
tip2015heapSortPermutessmt2toList
  (Isaplannerprop54smt2S z52) Tip2015heapSortPermutessmt2Nil =
  Nil :: Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
tip2015heapSortPermutessmt2insert2 ::
  Isaplannerprop54smt2Nat ->
    Tip2015heapSortPermutessmt2Heap -> Tip2015heapSortPermutessmt2Heap
tip2015heapSortPermutessmt2insert2 x57 y57 =
  tip2015heapSortPermutessmt2merge
    (Tip2015heapSortPermutessmt2Node
       Tip2015heapSortPermutessmt2Nil x57 Tip2015heapSortPermutessmt2Nil)
    y57
tip2015heapSortPermutessmt2toHeap ::
  Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
    Tip2015heapSortPermutessmt2Heap
tip2015heapSortPermutessmt2toHeap Nil =
  Tip2015heapSortPermutessmt2Nil
tip2015heapSortPermutessmt2toHeap (Cons y58 xs28) =
  tip2015heapSortPermutessmt2insert2
    y58 (tip2015heapSortPermutessmt2toHeap xs28)
heapSize ::
  Tip2015heapSortPermutessmt2Heap -> Isaplannerprop54smt2Nat
heapSize (Tip2015heapSortPermutessmt2Node l3 y59 r2) =
  Isaplannerprop54smt2S
    (isaplannerprop54smt2plus (heapSize l3) (heapSize r2))
heapSize Tip2015heapSortPermutessmt2Nil = Isaplannerprop54smt2Z
toList2 ::
  Tip2015heapSortPermutessmt2Heap ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
toList2 x58 = tip2015heapSortPermutessmt2toList (heapSize x58) x58
tip2015heapSortPermutessmt2hsort ::
  Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
tip2015heapSortPermutessmt2hsort x59 =
  toList2 (tip2015heapSortPermutessmt2toHeap x59)
deeps :: Tip2015regexpRecPlussmt2R -> Tip2015regexpRecPlussmt2R
deeps Tip2015regexpRecPlussmt2Nil = Tip2015regexpRecPlussmt2Nil
deeps Eps = Tip2015regexpRecPlussmt2Nil
deeps (Tip2015regexpRecPlussmt2Atom a38) =
  Tip2015regexpRecPlussmt2Atom a38
deeps (Tip2015regexpRecPlussmt2Plus p4 q6) =
  Tip2015regexpRecPlussmt2Plus (deeps p4) (deeps q6)
deeps (Tip2015regexpRecPlussmt2Seq p23 q26) =
  case (tip2015regexpRecPlussmt2eps p23) P.&&
         (tip2015regexpRecPlussmt2eps q26) of
    P.True -> Tip2015regexpRecPlussmt2Plus (deeps p23) (deeps q26)
    P.False -> Tip2015regexpRecPlussmt2Seq p23 q26
deeps (Tip2015regexpRecPlussmt2Star p33) = deeps p33
tip2015sortSSortSortssmt2zisaplannerprop78smt2sorted ::
  Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortSSortSortssmt2zisaplannerprop78smt2sorted Nil = P.True
tip2015sortSSortSortssmt2zisaplannerprop78smt2sorted
  (Cons y60 Nil) =
  P.True
tip2015sortSSortSortssmt2zisaplannerprop78smt2sorted
  (Cons y60 (Cons y214 xs29)) =
  (y60 P.<= y214) P.&&
    (tip2015sortSSortSortssmt2zisaplannerprop78smt2sorted
       (Cons y214 xs29))
tip2015sortSSortSortssmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortSortssmt2zdelete x60 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortSortssmt2zdelete x60 (Cons z53 ys10) =
  case x60 P.== z53 of
    P.True -> ys10
    P.False -> Cons z53 (tip2015sortSSortSortssmt2zdelete x60 ys10)
tip2015sortSSortSortssmt2ssortminimum ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Int
tip2015sortSSortSortssmt2ssortminimum x61 Nil = x61
tip2015sortSSortSortssmt2ssortminimum x61 (Cons z54 ys11) =
  case z54 P.<= x61 of
    P.True -> tip2015sortSSortSortssmt2ssortminimum z54 ys11
    P.False -> tip2015sortSSortSortssmt2ssortminimum x61 ys11
tip2015sortSSortSortssmt2ssort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortSortssmt2ssort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortSortssmt2ssort (Cons y61 ys12) =
  let m5 = tip2015sortSSortSortssmt2ssortminimum y61 ys12
    in Cons
         m5
         (tip2015sortSSortSortssmt2ssort
            (tip2015sortSSortSortssmt2zdelete m5 (Cons y61 ys12)))
sum :: Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
sum Isaplannerprop54smt2Z = Isaplannerprop54smt2Z
sum (Isaplannerprop54smt2S n5) =
  isaplannerprop54smt2plus (sum n5) (Isaplannerprop54smt2S n5)
cubes :: Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
cubes Isaplannerprop54smt2Z = Isaplannerprop54smt2Z
cubes (Isaplannerprop54smt2S n6) =
  isaplannerprop54smt2plus
    (cubes n6)
    (tip2015nataltmulsamesmt2mult
       (tip2015nataltmulsamesmt2mult
          (Isaplannerprop54smt2S n6) (Isaplannerprop54smt2S n6))
       (Isaplannerprop54smt2S n6))
tip2015natboringgereflexivesmt2ge ::
  Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat -> P.Bool
tip2015natboringgereflexivesmt2ge x64 Isaplannerprop54smt2Z =
  P.True
tip2015natboringgereflexivesmt2ge
  Isaplannerprop54smt2Z (Isaplannerprop54smt2S z55) =
  P.False
tip2015natboringgereflexivesmt2ge
  (Isaplannerprop54smt2S x228) (Isaplannerprop54smt2S z55) =
  tip2015natboringgereflexivesmt2ge x228 z55
tip2015weirdnatopspecsmt2op ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat ->
      Isaplannerprop54smt2Nat ->
        Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
tip2015weirdnatopspecsmt2op
  Isaplannerprop54smt2Z y62 Isaplannerprop54smt2Z x229 =
  x229
tip2015weirdnatopspecsmt2op
  Isaplannerprop54smt2Z y62 (Isaplannerprop54smt2S x315) x229 =
  tip2015weirdnatopspecsmt2op
    Isaplannerprop54smt2Z y62 x315 (Isaplannerprop54smt2S x229)
tip2015weirdnatopspecsmt2op
  (Isaplannerprop54smt2S x413) y62 Isaplannerprop54smt2Z x229 =
  tip2015weirdnatopspecsmt2op x413 y62 y62 x229
tip2015weirdnatopspecsmt2op
  (Isaplannerprop54smt2S x413) y62 (Isaplannerprop54smt2S c2) x229 =
  tip2015weirdnatopspecsmt2op
    (Isaplannerprop54smt2S x413) y62 c2 (Isaplannerprop54smt2S x229)
tip2015propositionalSoundsmt2models4 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list
      (Isaplannerprop45smt2Pair P.Int P.Bool) ->
      Grammarssimpexprunambig3smt2list P.Bool
tip2015propositionalSoundsmt2models4 x65 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Bool
tip2015propositionalSoundsmt2models4
  x65 (Cons (Pair2 y215 P.True) x230) =
  tip2015propositionalSoundsmt2models4 x65 x230
tip2015propositionalSoundsmt2models4
  x65 (Cons (Pair2 y215 P.False) x230) =
  Cons
    (x65 P.== y215) (tip2015propositionalSoundsmt2models4 x65 x230)
tip2015propositionalSoundsmt2models3 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list
      (Isaplannerprop45smt2Pair P.Int P.Bool) ->
      Grammarssimpexprunambig3smt2list P.Bool
tip2015propositionalSoundsmt2models3 x66 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Bool
tip2015propositionalSoundsmt2models3
  x66 (Cons (Pair2 y216 P.True) x231) =
  Cons
    (x66 P.== y216) (tip2015propositionalSoundsmt2models3 x66 x231)
tip2015propositionalSoundsmt2models3
  x66 (Cons (Pair2 y216 P.False) x231) =
  tip2015propositionalSoundsmt2models3 x66 x231
all ::
  (a39 -> P.Bool) -> Grammarssimpexprunambig3smt2list a39 -> P.Bool
all x67 Nil = P.True
all x67 (Cons z56 xs30) = (P.id x67 z56) P.&& (all x67 xs30)
flatten3 ::
  Tip2015treesortAddSamesmt2Tree a40 ->
    Grammarssimpexprunambig3smt2list a40
flatten3
  (Tip2015treesortAddSamesmt2Node
     (Tip2015treesortAddSamesmt2Node p5 x232 q7) z57 r3) =
  flatten3
    (Tip2015treesortAddSamesmt2Node
       p5 x232 (Tip2015treesortAddSamesmt2Node q7 z57 r3))
flatten3
  (Tip2015treesortAddSamesmt2Node
     Tip2015treesortAddSamesmt2Nil z57 r3) =
  Cons z57 (flatten3 r3)
flatten3 Tip2015treesortAddSamesmt2Nil =
  Nil :: Grammarssimpexprunambig3smt2list a40
flatten0 ::
  Tip2015treesortAddSamesmt2Tree a41 ->
    Grammarssimpexprunambig3smt2list a41
flatten0 (Tip2015treesortAddSamesmt2Node p6 y63 q8) =
  append
    (append
       (flatten0 p6)
       (Cons y63 (Nil :: Grammarssimpexprunambig3smt2list a41)))
    (flatten0 q8)
flatten0 Tip2015treesortAddSamesmt2Nil =
  Nil :: Grammarssimpexprunambig3smt2list a41
tip2015sortNStoogeSort2Countsmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015sortNStoogeSort2Countsmt2zcount x68 Nil =
  Isaplannerprop54smt2Z
tip2015sortNStoogeSort2Countsmt2zcount x68 (Cons z58 xs31) =
  case x68 P.== z58 of
    P.True ->
      Isaplannerprop54smt2S
        (tip2015sortNStoogeSort2Countsmt2zcount x68 xs31)
    P.False -> tip2015sortNStoogeSort2Countsmt2zcount x68 xs31
twoThirds :: Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
twoThirds Isaplannerprop54smt2Z = Isaplannerprop54smt2Z
twoThirds (Isaplannerprop54smt2S Isaplannerprop54smt2Z) =
  Isaplannerprop54smt2S Isaplannerprop54smt2Z
twoThirds
  (Isaplannerprop54smt2S
     (Isaplannerprop54smt2S Isaplannerprop54smt2Z)) =
  Isaplannerprop54smt2S Isaplannerprop54smt2Z
twoThirds
  (Isaplannerprop54smt2S
     (Isaplannerprop54smt2S (Isaplannerprop54smt2S n7))) =
  Isaplannerprop54smt2S (Isaplannerprop54smt2S (twoThirds n7))
third :: Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
third Isaplannerprop54smt2Z = Isaplannerprop54smt2Z
third (Isaplannerprop54smt2S Isaplannerprop54smt2Z) =
  Isaplannerprop54smt2Z
third
  (Isaplannerprop54smt2S
     (Isaplannerprop54smt2S Isaplannerprop54smt2Z)) =
  Isaplannerprop54smt2Z
third
  (Isaplannerprop54smt2S
     (Isaplannerprop54smt2S (Isaplannerprop54smt2S n8))) =
  Isaplannerprop54smt2S (third n8)
tip2015sortNStoogeSort2Countsmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2Countsmt2sort2 x69 y64 =
  case x69 P.<= y64 of
    P.True ->
      Cons x69 (Cons y64 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons y64 (Cons x69 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortNStoogeSort2Countsmt2splitAt ::
  Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list a42 ->
      Isaplannerprop45smt2Pair
        (Grammarssimpexprunambig3smt2list a42)
        (Grammarssimpexprunambig3smt2list a42)
tip2015sortNStoogeSort2Countsmt2splitAt x70 y65 =
  Pair2
    (isaplannerprop82smt2take x70 y65)
    (isaplannerprop12smt2drop x70 y65)
tip2015sortNStoogeSort2Countsmt2nstooge2sort2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2Countsmt2nstooge2sort2 x71 =
  case tip2015sortNStoogeSort2Countsmt2splitAt
         (twoThirds (isaplannerprop68smt2len x71)) x71 of
    Pair2 ys13 zs2 ->
      append (tip2015sortNStoogeSort2Countsmt2nstoogesort2 ys13) zs2
tip2015sortNStoogeSort2Countsmt2nstoogesort2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2Countsmt2nstoogesort2 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2Countsmt2nstoogesort2 (Cons y66 Nil) =
  Cons y66 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortNStoogeSort2Countsmt2nstoogesort2
  (Cons y66 (Cons y217 Nil)) =
  tip2015sortNStoogeSort2Countsmt2sort2 y66 y217
tip2015sortNStoogeSort2Countsmt2nstoogesort2
  (Cons y66 (Cons y217 (Cons x316 x414))) =
  tip2015sortNStoogeSort2Countsmt2nstooge2sort2
    (tip2015sortNStoogeSort2Countsmt2nstooge2sort1
       (tip2015sortNStoogeSort2Countsmt2nstooge2sort2
          (Cons y66 (Cons y217 (Cons x316 x414)))))
tip2015sortNStoogeSort2Countsmt2nstooge2sort1 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2Countsmt2nstooge2sort1 x73 =
  case tip2015sortNStoogeSort2Countsmt2splitAt
         (third (isaplannerprop68smt2len x73)) x73 of
    Pair2 ys14 zs3 ->
      append ys14 (tip2015sortNStoogeSort2Countsmt2nstoogesort2 zs3)
tip2015binplussmt2s :: Bin -> Bin
tip2015binplussmt2s Tip2015binplussmt2One =
  Tip2015binplussmt2ZeroAnd Tip2015binplussmt2One
tip2015binplussmt2s (Tip2015binplussmt2ZeroAnd xs32) =
  Tip2015binplussmt2OneAnd xs32
tip2015binplussmt2s (Tip2015binplussmt2OneAnd ys15) =
  Tip2015binplussmt2ZeroAnd (tip2015binplussmt2s ys15)
toNat :: Bin -> Isaplannerprop54smt2Nat
toNat Tip2015binplussmt2One =
  Isaplannerprop54smt2S Isaplannerprop54smt2Z
toNat (Tip2015binplussmt2ZeroAnd xs33) =
  isaplannerprop54smt2plus (toNat xs33) (toNat xs33)
toNat (Tip2015binplussmt2OneAnd ys16) =
  Isaplannerprop54smt2S
    (isaplannerprop54smt2plus (toNat ys16) (toNat ys16))
tip2015binplussmt2plus :: Bin -> Bin -> Bin
tip2015binplussmt2plus Tip2015binplussmt2One y67 =
  tip2015binplussmt2s y67
tip2015binplussmt2plus
  (Tip2015binplussmt2ZeroAnd z59) Tip2015binplussmt2One =
  tip2015binplussmt2s (Tip2015binplussmt2ZeroAnd z59)
tip2015binplussmt2plus
  (Tip2015binplussmt2ZeroAnd z59) (Tip2015binplussmt2ZeroAnd ys17) =
  Tip2015binplussmt2ZeroAnd (tip2015binplussmt2plus z59 ys17)
tip2015binplussmt2plus
  (Tip2015binplussmt2ZeroAnd z59) (Tip2015binplussmt2OneAnd xs34) =
  Tip2015binplussmt2OneAnd (tip2015binplussmt2plus z59 xs34)
tip2015binplussmt2plus
  (Tip2015binplussmt2OneAnd x233) Tip2015binplussmt2One =
  tip2015binplussmt2s (Tip2015binplussmt2OneAnd x233)
tip2015binplussmt2plus
  (Tip2015binplussmt2OneAnd x233) (Tip2015binplussmt2ZeroAnd zs4) =
  Tip2015binplussmt2OneAnd (tip2015binplussmt2plus x233 zs4)
tip2015binplussmt2plus
  (Tip2015binplussmt2OneAnd x233) (Tip2015binplussmt2OneAnd ys22) =
  Tip2015binplussmt2ZeroAnd
    (tip2015binplussmt2s (tip2015binplussmt2plus x233 ys22))
tip2015listelemnubrsmt2nub ::
  Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
tip2015listelemnubrsmt2nub Nil =
  Nil :: Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
tip2015listelemnubrsmt2nub (Cons y68 xs35) =
  Cons
    y68
    (isaplannerprop37smt2delete y68 (tip2015listelemnubrsmt2nub xs35))
tip2015listSelectPermutationssmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015listSelectPermutationssmt2zelem x74 Nil = P.False
tip2015listSelectPermutationssmt2zelem x74 (Cons z60 ys18) =
  (x74 P.== z60) P.||
    (tip2015listSelectPermutationssmt2zelem x74 ys18)
tip2015listSelectPermutationssmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015listSelectPermutationssmt2zdelete x75 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015listSelectPermutationssmt2zdelete x75 (Cons z61 ys19) =
  case x75 P.== z61 of
    P.True -> ys19
    P.False ->
      Cons z61 (tip2015listSelectPermutationssmt2zdelete x75 ys19)
select3 ::
  a43 ->
    Grammarssimpexprunambig3smt2list
      (Isaplannerprop45smt2Pair
         a43 (Grammarssimpexprunambig3smt2list a43)) ->
      Grammarssimpexprunambig3smt2list
        (Isaplannerprop45smt2Pair
           a43 (Grammarssimpexprunambig3smt2list a43))
select3 x76 Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Isaplannerprop45smt2Pair
         a43 (Grammarssimpexprunambig3smt2list a43))
select3 x76 (Cons (Pair2 y218 ys20) x234) =
  Cons (Pair2 y218 (Cons x76 ys20)) (select3 x76 x234)
select2 ::
  Grammarssimpexprunambig3smt2list a44 ->
    Grammarssimpexprunambig3smt2list
      (Isaplannerprop45smt2Pair
         a44 (Grammarssimpexprunambig3smt2list a44))
select2 Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Isaplannerprop45smt2Pair
         a44 (Grammarssimpexprunambig3smt2list a44))
select2 (Cons y69 xs36) =
  Cons (Pair2 y69 xs36) (select3 y69 (select2 xs36))
tip2015listSelectPermutationssmt2propSelectPermutations ::
  Grammarssimpexprunambig3smt2list
    (Isaplannerprop45smt2Pair
       P.Int (Grammarssimpexprunambig3smt2list P.Int)) ->
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015listSelectPermutationssmt2propSelectPermutations Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015listSelectPermutationssmt2propSelectPermutations
  (Cons (Pair2 y219 ys21) z62) =
  Cons
    (Cons y219 ys21)
    (tip2015listSelectPermutationssmt2propSelectPermutations z62)
tip2015listSelectPermutationssmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015listSelectPermutationssmt2zisPermutation Nil y70 = null y70
tip2015listSelectPermutationssmt2zisPermutation
  (Cons z63 xs37) y70 =
  (tip2015listSelectPermutationssmt2zelem z63 y70) P.&&
    (tip2015listSelectPermutationssmt2zisPermutation
       xs37 (tip2015listSelectPermutationssmt2zdelete z63 y70))
tip2015sortQSortPermutessmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortQSortPermutessmt2zelem x77 Nil = P.False
tip2015sortQSortPermutessmt2zelem x77 (Cons z64 ys23) =
  (x77 P.== z64) P.|| (tip2015sortQSortPermutessmt2zelem x77 ys23)
tip2015sortQSortPermutessmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortQSortPermutessmt2zdelete x78 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortQSortPermutessmt2zdelete x78 (Cons z65 ys24) =
  case x78 P.== z65 of
    P.True -> ys24
    P.False -> Cons z65 (tip2015sortQSortPermutessmt2zdelete x78 ys24)
tip2015sortQSortPermutessmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortQSortPermutessmt2zisPermutation Nil y71 = null y71
tip2015sortQSortPermutessmt2zisPermutation (Cons z66 xs38) y71 =
  (tip2015sortQSortPermutessmt2zelem z66 y71) P.&&
    (tip2015sortQSortPermutessmt2zisPermutation
       xs38 (tip2015sortQSortPermutessmt2zdelete z66 y71))
mul3acc ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat ->
      Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
mul3acc Isaplannerprop54smt2Z y72 z67 = Isaplannerprop54smt2Z
mul3acc (Isaplannerprop54smt2S x235) Isaplannerprop54smt2Z z67 =
  Isaplannerprop54smt2Z
mul3acc
  (Isaplannerprop54smt2S x235) (Isaplannerprop54smt2S x317)
  Isaplannerprop54smt2Z =
  Isaplannerprop54smt2Z
mul3acc
  (Isaplannerprop54smt2S Isaplannerprop54smt2Z)
  (Isaplannerprop54smt2S Isaplannerprop54smt2Z)
  (Isaplannerprop54smt2S Isaplannerprop54smt2Z) =
  Isaplannerprop54smt2S Isaplannerprop54smt2Z
mul3acc
  (Isaplannerprop54smt2S Isaplannerprop54smt2Z)
  (Isaplannerprop54smt2S Isaplannerprop54smt2Z)
  (Isaplannerprop54smt2S (Isaplannerprop54smt2S x510)) =
  Isaplannerprop54smt2S
    (add3acc
       (mul3acc
          Isaplannerprop54smt2Z Isaplannerprop54smt2Z
          (Isaplannerprop54smt2S x510))
       (add3acc
          (mul3acc
             (Isaplannerprop54smt2S Isaplannerprop54smt2Z) Isaplannerprop54smt2Z
             (Isaplannerprop54smt2S x510))
          (mul3acc
             Isaplannerprop54smt2Z (Isaplannerprop54smt2S Isaplannerprop54smt2Z)
             (Isaplannerprop54smt2S x510))
          (mul3acc
             Isaplannerprop54smt2Z Isaplannerprop54smt2Z
             (Isaplannerprop54smt2S Isaplannerprop54smt2Z)))
       (add3acc
          Isaplannerprop54smt2Z Isaplannerprop54smt2Z
          (Isaplannerprop54smt2S x510)))
mul3acc
  (Isaplannerprop54smt2S Isaplannerprop54smt2Z)
  (Isaplannerprop54smt2S (Isaplannerprop54smt2S x610))
  (Isaplannerprop54smt2S x415) =
  Isaplannerprop54smt2S
    (add3acc
       (mul3acc Isaplannerprop54smt2Z (Isaplannerprop54smt2S x610) x415)
       (add3acc
          (mul3acc
             (Isaplannerprop54smt2S Isaplannerprop54smt2Z)
             (Isaplannerprop54smt2S x610) x415)
          (mul3acc
             Isaplannerprop54smt2Z (Isaplannerprop54smt2S Isaplannerprop54smt2Z)
             x415)
          (mul3acc
             Isaplannerprop54smt2Z (Isaplannerprop54smt2S x610)
             (Isaplannerprop54smt2S Isaplannerprop54smt2Z)))
       (add3acc Isaplannerprop54smt2Z (Isaplannerprop54smt2S x610) x415))
mul3acc
  (Isaplannerprop54smt2S (Isaplannerprop54smt2S x79))
  (Isaplannerprop54smt2S x317) (Isaplannerprop54smt2S x415) =
  Isaplannerprop54smt2S
    (add3acc
       (mul3acc (Isaplannerprop54smt2S x79) x317 x415)
       (add3acc
          (mul3acc (Isaplannerprop54smt2S Isaplannerprop54smt2Z) x317 x415)
          (mul3acc
             (Isaplannerprop54smt2S x79)
             (Isaplannerprop54smt2S Isaplannerprop54smt2Z) x415)
          (mul3acc
             (Isaplannerprop54smt2S x79) x317
             (Isaplannerprop54smt2S Isaplannerprop54smt2Z)))
       (add3acc (Isaplannerprop54smt2S x79) x317 x415))
unpair ::
  Grammarssimpexprunambig3smt2list (Isaplannerprop45smt2Pair s s) ->
    Grammarssimpexprunambig3smt2list s
unpair Nil = Nil :: Grammarssimpexprunambig3smt2list s
unpair (Cons (Pair2 z68 y220) xys) =
  Cons z68 (Cons y220 (unpair xys))
tip2015listPairUnpairsmt2pairs ::
  Grammarssimpexprunambig3smt2list t2 ->
    Grammarssimpexprunambig3smt2list (Isaplannerprop45smt2Pair t2 t2)
tip2015listPairUnpairsmt2pairs Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list (Isaplannerprop45smt2Pair t2 t2)
tip2015listPairUnpairsmt2pairs (Cons y73 Nil) =
  Nil ::
    Grammarssimpexprunambig3smt2list (Isaplannerprop45smt2Pair t2 t2)
tip2015listPairUnpairsmt2pairs (Cons y73 (Cons y221 xs39)) =
  Cons (Pair2 y73 y221) (tip2015listPairUnpairsmt2pairs xs39)
even :: Isaplannerprop54smt2Nat -> P.Bool
even Isaplannerprop54smt2Z = P.True
even (Isaplannerprop54smt2S Isaplannerprop54smt2Z) = P.False
even (Isaplannerprop54smt2S (Isaplannerprop54smt2S z69)) = even z69
weirdconcat ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list a45) ->
    Grammarssimpexprunambig3smt2list a45
weirdconcat Nil = Nil :: Grammarssimpexprunambig3smt2list a45
weirdconcat (Cons Nil xss3) = weirdconcat xss3
weirdconcat (Cons (Cons z70 xs40) xss3) =
  Cons z70 (weirdconcat (Cons xs40 xss3))
tip2015listzpermelemsmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015listzpermelemsmt2zelem x80 Nil = P.False
tip2015listzpermelemsmt2zelem x80 (Cons z71 ys25) =
  (x80 P.== z71) P.|| (tip2015listzpermelemsmt2zelem x80 ys25)
tip2015listzpermelemsmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015listzpermelemsmt2zdelete x81 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015listzpermelemsmt2zdelete x81 (Cons z72 ys26) =
  case x81 P.== z72 of
    P.True -> ys26
    P.False -> Cons z72 (tip2015listzpermelemsmt2zdelete x81 ys26)
tip2015listzpermelemsmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015listzpermelemsmt2zisPermutation Nil y74 = null y74
tip2015listzpermelemsmt2zisPermutation (Cons z73 xs41) y74 =
  (tip2015listzpermelemsmt2zelem z73 y74) P.&&
    (tip2015listzpermelemsmt2zisPermutation
       xs41 (tip2015listzpermelemsmt2zdelete z73 y74))
tip2015sortMSortTDPermutessmt2ztake ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a46 ->
      Grammarssimpexprunambig3smt2list a46
tip2015sortMSortTDPermutessmt2ztake x82 y75 =
  case x82 P.== (0) of
    P.True -> Nil :: Grammarssimpexprunambig3smt2list a46
    P.False ->
      case y75 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a46
        Cons z74 xs42 ->
          Cons z74 (tip2015sortMSortTDPermutessmt2ztake (x82 P.- (1)) xs42)
tip2015sortMSortTDPermutessmt2zlength ::
  Grammarssimpexprunambig3smt2list a47 -> P.Int
tip2015sortMSortTDPermutessmt2zlength Nil = 0
tip2015sortMSortTDPermutessmt2zlength (Cons y76 xs43) =
  (1) P.+ (tip2015sortMSortTDPermutessmt2zlength xs43)
tip2015sortMSortTDPermutessmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortMSortTDPermutessmt2zelem x83 Nil = P.False
tip2015sortMSortTDPermutessmt2zelem x83 (Cons z75 ys27) =
  (x83 P.== z75) P.|| (tip2015sortMSortTDPermutessmt2zelem x83 ys27)
tip2015sortMSortTDPermutessmt2zdrop ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a48 ->
      Grammarssimpexprunambig3smt2list a48
tip2015sortMSortTDPermutessmt2zdrop x84 y77 =
  case x84 P.== (0) of
    P.True -> y77
    P.False ->
      case y77 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a48
        Cons z76 xs110 ->
          tip2015sortMSortTDPermutessmt2zdrop (x84 P.- (1)) xs110
tip2015sortMSortTDPermutessmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortTDPermutessmt2zdelete x85 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortTDPermutessmt2zdelete x85 (Cons z77 ys28) =
  case x85 P.== z77 of
    P.True -> ys28
    P.False ->
      Cons z77 (tip2015sortMSortTDPermutessmt2zdelete x85 ys28)
tip2015sortMSortTDPermutessmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortMSortTDPermutessmt2zisPermutation Nil y78 = null y78
tip2015sortMSortTDPermutessmt2zisPermutation (Cons z78 xs44) y78 =
  (tip2015sortMSortTDPermutessmt2zelem z78 y78) P.&&
    (tip2015sortMSortTDPermutessmt2zisPermutation
       xs44 (tip2015sortMSortTDPermutessmt2zdelete z78 y78))
tip2015sortMSortTDPermutessmt2lmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortTDPermutessmt2lmerge Nil y79 = y79
tip2015sortMSortTDPermutessmt2lmerge (Cons z79 x236) Nil =
  Cons z79 x236
tip2015sortMSortTDPermutessmt2lmerge
  (Cons z79 x236) (Cons x318 x416) =
  case z79 P.<= x318 of
    P.True ->
      Cons
        z79 (tip2015sortMSortTDPermutessmt2lmerge x236 (Cons x318 x416))
    P.False ->
      Cons
        x318 (tip2015sortMSortTDPermutessmt2lmerge (Cons z79 x236) x416)
tip2015sortMSortTDPermutessmt2msorttd ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortTDPermutessmt2msorttd Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortTDPermutessmt2msorttd (Cons y80 Nil) =
  Cons y80 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortTDPermutessmt2msorttd (Cons y80 (Cons x237 x319)) =
  let j =
        P.div
          (tip2015sortMSortTDPermutessmt2zlength (Cons y80 (Cons x237 x319)))
          (2)
    in tip2015sortMSortTDPermutessmt2lmerge
         (tip2015sortMSortTDPermutessmt2msorttd
            (tip2015sortMSortTDPermutessmt2ztake
               j (Cons y80 (Cons x237 x319))))
         (tip2015sortMSortTDPermutessmt2msorttd
            (tip2015sortMSortTDPermutessmt2zdrop
               j (Cons y80 (Cons x237 x319))))
tip2015sortStoogeSort2Permutessmt2ztake ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a49 ->
      Grammarssimpexprunambig3smt2list a49
tip2015sortStoogeSort2Permutessmt2ztake x86 y81 =
  case x86 P.== (0) of
    P.True -> Nil :: Grammarssimpexprunambig3smt2list a49
    P.False ->
      case y81 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a49
        Cons z80 xs45 ->
          Cons
            z80 (tip2015sortStoogeSort2Permutessmt2ztake (x86 P.- (1)) xs45)
tip2015sortStoogeSort2Permutessmt2zlength ::
  Grammarssimpexprunambig3smt2list a50 -> P.Int
tip2015sortStoogeSort2Permutessmt2zlength Nil = 0
tip2015sortStoogeSort2Permutessmt2zlength (Cons y82 xs46) =
  (1) P.+ (tip2015sortStoogeSort2Permutessmt2zlength xs46)
tip2015sortStoogeSort2Permutessmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortStoogeSort2Permutessmt2zelem x87 Nil = P.False
tip2015sortStoogeSort2Permutessmt2zelem x87 (Cons z81 ys29) =
  (x87 P.== z81) P.||
    (tip2015sortStoogeSort2Permutessmt2zelem x87 ys29)
tip2015sortStoogeSort2Permutessmt2zdrop ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a51 ->
      Grammarssimpexprunambig3smt2list a51
tip2015sortStoogeSort2Permutessmt2zdrop x88 y83 =
  case x88 P.== (0) of
    P.True -> y83
    P.False ->
      case y83 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a51
        Cons z82 xs111 ->
          tip2015sortStoogeSort2Permutessmt2zdrop (x88 P.- (1)) xs111
tip2015sortStoogeSort2Permutessmt2zsplitAt ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a52 ->
      Isaplannerprop45smt2Pair
        (Grammarssimpexprunambig3smt2list a52)
        (Grammarssimpexprunambig3smt2list a52)
tip2015sortStoogeSort2Permutessmt2zsplitAt x89 y84 =
  Pair2
    (tip2015sortStoogeSort2Permutessmt2ztake x89 y84)
    (tip2015sortStoogeSort2Permutessmt2zdrop x89 y84)
tip2015sortStoogeSort2Permutessmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSort2Permutessmt2zdelete x90 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSort2Permutessmt2zdelete x90 (Cons z83 ys30) =
  case x90 P.== z83 of
    P.True -> ys30
    P.False ->
      Cons z83 (tip2015sortStoogeSort2Permutessmt2zdelete x90 ys30)
tip2015sortStoogeSort2Permutessmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSort2Permutessmt2sort2 x91 y85 =
  case x91 P.<= y85 of
    P.True ->
      Cons x91 (Cons y85 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons y85 (Cons x91 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortStoogeSort2Permutessmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortStoogeSort2Permutessmt2zisPermutation Nil y86 = null y86
tip2015sortStoogeSort2Permutessmt2zisPermutation
  (Cons z84 xs47) y86 =
  (tip2015sortStoogeSort2Permutessmt2zelem z84 y86) P.&&
    (tip2015sortStoogeSort2Permutessmt2zisPermutation
       xs47 (tip2015sortStoogeSort2Permutessmt2zdelete z84 y86))
tip2015rotatesnocsmt2snoc ::
  a53 ->
    Grammarssimpexprunambig3smt2list a53 ->
      Grammarssimpexprunambig3smt2list a53
tip2015rotatesnocsmt2snoc x92 Nil =
  Cons x92 (Nil :: Grammarssimpexprunambig3smt2list a53)
tip2015rotatesnocsmt2snoc x92 (Cons z85 ys31) =
  Cons z85 (tip2015rotatesnocsmt2snoc x92 ys31)
tip2015rotatesnocsmt2rotate ::
  Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list a54 ->
      Grammarssimpexprunambig3smt2list a54
tip2015rotatesnocsmt2rotate Isaplannerprop54smt2Z y87 = y87
tip2015rotatesnocsmt2rotate (Isaplannerprop54smt2S z86) Nil =
  Nil :: Grammarssimpexprunambig3smt2list a54
tip2015rotatesnocsmt2rotate
  (Isaplannerprop54smt2S z86) (Cons x238 x320) =
  tip2015rotatesnocsmt2rotate
    z86 (tip2015rotatesnocsmt2snoc x238 x320)
tip2015sortBubSortPermutessmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortBubSortPermutessmt2zelem x93 Nil = P.False
tip2015sortBubSortPermutessmt2zelem x93 (Cons z87 ys32) =
  (x93 P.== z87) P.|| (tip2015sortBubSortPermutessmt2zelem x93 ys32)
tip2015sortBubSortPermutessmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortBubSortPermutessmt2zdelete x94 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortBubSortPermutessmt2zdelete x94 (Cons z88 ys33) =
  case x94 P.== z88 of
    P.True -> ys33
    P.False ->
      Cons z88 (tip2015sortBubSortPermutessmt2zdelete x94 ys33)
tip2015sortBubSortPermutessmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortBubSortPermutessmt2zisPermutation Nil y88 = null y88
tip2015sortBubSortPermutessmt2zisPermutation (Cons z89 xs48) y88 =
  (tip2015sortBubSortPermutessmt2zelem z89 y88) P.&&
    (tip2015sortBubSortPermutessmt2zisPermutation
       xs48 (tip2015sortBubSortPermutessmt2zdelete z89 y88))
tip2015sortBubSortPermutessmt2bubble ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Isaplannerprop45smt2Pair
      P.Bool (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortBubSortPermutessmt2bubble Nil =
  Pair2 P.False (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortBubSortPermutessmt2bubble (Cons y89 Nil) =
  Pair2
    P.False (Cons y89 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortBubSortPermutessmt2bubble (Cons y89 (Cons y222 xs49)) =
  case y89 P.<= y222 of
    P.True ->
      case tip2015sortBubSortPermutessmt2bubble (Cons y222 xs49) of
        Pair2 b22 zs5 -> Pair2 b22 (Cons y89 zs5)
    P.False ->
      case tip2015sortBubSortPermutessmt2bubble (Cons y89 xs49) of
        Pair2 c3 ys34 -> Pair2 P.True (Cons y222 ys34)
tip2015sortBubSortPermutessmt2bubsort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortBubSortPermutessmt2bubsort x95 =
  case tip2015sortBubSortPermutessmt2bubble x95 of
    Pair2 c4 ys35 ->
      case c4 of
        P.True -> tip2015sortBubSortPermutessmt2bubsort ys35
        P.False -> x95
tip2015sortMSortBUIsSortsmt2lmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUIsSortsmt2lmerge Nil y90 = y90
tip2015sortMSortBUIsSortsmt2lmerge (Cons z90 x239) Nil =
  Cons z90 x239
tip2015sortMSortBUIsSortsmt2lmerge
  (Cons z90 x239) (Cons x321 x417) =
  case z90 P.<= x321 of
    P.True ->
      Cons z90 (tip2015sortMSortBUIsSortsmt2lmerge x239 (Cons x321 x417))
    P.False ->
      Cons x321 (tip2015sortMSortBUIsSortsmt2lmerge (Cons z90 x239) x417)
tip2015sortMSortBUIsSortsmt2pairwise ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list P.Int) ->
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBUIsSortsmt2pairwise Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBUIsSortsmt2pairwise (Cons xs50 Nil) =
  Cons
    xs50
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Grammarssimpexprunambig3smt2list P.Int))
tip2015sortMSortBUIsSortsmt2pairwise (Cons xs50 (Cons ys36 xss4)) =
  Cons
    (tip2015sortMSortBUIsSortsmt2lmerge xs50 ys36)
    (tip2015sortMSortBUIsSortsmt2pairwise xss4)
tip2015sortMSortBUIsSortsmt2mergingbu ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list P.Int) ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUIsSortsmt2mergingbu Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUIsSortsmt2mergingbu (Cons xs51 Nil) = xs51
tip2015sortMSortBUIsSortsmt2mergingbu (Cons xs51 (Cons z91 x240)) =
  tip2015sortMSortBUIsSortsmt2mergingbu
    (tip2015sortMSortBUIsSortsmt2pairwise (Cons xs51 (Cons z91 x240)))
tip2015sortMSortBUIsSortsmt2msortbu ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUIsSortsmt2msortbu x96 =
  tip2015sortMSortBUIsSortsmt2mergingbu
    (map2
       (\ y91 -> Cons y91 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
       x96)
tip2015sortMSortBUIsSortsmt2insert2 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUIsSortsmt2insert2 x97 Nil =
  Cons x97 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBUIsSortsmt2insert2 x97 (Cons z92 xs52) =
  case x97 P.<= z92 of
    P.True -> Cons x97 (Cons z92 xs52)
    P.False -> Cons z92 (tip2015sortMSortBUIsSortsmt2insert2 x97 xs52)
tip2015sortMSortBUIsSortsmt2isort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUIsSortsmt2isort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUIsSortsmt2isort (Cons y92 xs53) =
  tip2015sortMSortBUIsSortsmt2insert2
    y92 (tip2015sortMSortBUIsSortsmt2isort xs53)
tip2015listzdeleteAllcountsmt2zdeleteAll ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015listzdeleteAllcountsmt2zdeleteAll x98 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015listzdeleteAllcountsmt2zdeleteAll x98 (Cons z93 xs54) =
  case x98 P.== z93 of
    P.True -> tip2015listzdeleteAllcountsmt2zdeleteAll x98 xs54
    P.False ->
      Cons z93 (tip2015listzdeleteAllcountsmt2zdeleteAll x98 xs54)
tip2015listzdeleteAllcountsmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015listzdeleteAllcountsmt2zdelete x99 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015listzdeleteAllcountsmt2zdelete x99 (Cons z94 ys37) =
  case x99 P.== z94 of
    P.True -> ys37
    P.False ->
      Cons z94 (tip2015listzdeleteAllcountsmt2zdelete x99 ys37)
tip2015listzdeleteAllcountsmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015listzdeleteAllcountsmt2zcount x100 Nil =
  Isaplannerprop54smt2Z
tip2015listzdeleteAllcountsmt2zcount x100 (Cons z95 xs55) =
  case x100 P.== z95 of
    P.True ->
      Isaplannerprop54smt2S
        (tip2015listzdeleteAllcountsmt2zcount x100 xs55)
    P.False -> tip2015listzdeleteAllcountsmt2zcount x100 xs55
tip2015listzpermsymmsmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015listzpermsymmsmt2zelem x101 Nil = P.False
tip2015listzpermsymmsmt2zelem x101 (Cons z96 ys38) =
  (x101 P.== z96) P.|| (tip2015listzpermsymmsmt2zelem x101 ys38)
tip2015listzpermsymmsmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015listzpermsymmsmt2zdelete x102 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015listzpermsymmsmt2zdelete x102 (Cons z97 ys39) =
  case x102 P.== z97 of
    P.True -> ys39
    P.False -> Cons z97 (tip2015listzpermsymmsmt2zdelete x102 ys39)
tip2015listzpermsymmsmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015listzpermsymmsmt2zisPermutation Nil y93 = null y93
tip2015listzpermsymmsmt2zisPermutation (Cons z98 xs56) y93 =
  (tip2015listzpermsymmsmt2zelem z98 y93) P.&&
    (tip2015listzpermsymmsmt2zisPermutation
       xs56 (tip2015listzpermsymmsmt2zdelete z98 y93))
tip2015sortMSortBU2Permutessmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortMSortBU2Permutessmt2zelem x103 Nil = P.False
tip2015sortMSortBU2Permutessmt2zelem x103 (Cons z99 ys40) =
  (x103 P.== z99) P.||
    (tip2015sortMSortBU2Permutessmt2zelem x103 ys40)
tip2015sortMSortBU2Permutessmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2Permutessmt2zdelete x104 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2Permutessmt2zdelete x104 (Cons z100 ys41) =
  case x104 P.== z100 of
    P.True -> ys41
    P.False ->
      Cons z100 (tip2015sortMSortBU2Permutessmt2zdelete x104 ys41)
tip2015sortMSortBU2Permutessmt2risers ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBU2Permutessmt2risers Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBU2Permutessmt2risers (Cons y94 Nil) =
  Cons
    (Cons y94 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Grammarssimpexprunambig3smt2list P.Int))
tip2015sortMSortBU2Permutessmt2risers (Cons y94 (Cons y223 xs57)) =
  case y94 P.<= y223 of
    P.True ->
      case tip2015sortMSortBU2Permutessmt2risers (Cons y223 xs57) of
        Nil ->
          Nil ::
            Grammarssimpexprunambig3smt2list
              (Grammarssimpexprunambig3smt2list P.Int)
        Cons ys42 yss2 -> Cons (Cons y94 ys42) yss2
    P.False ->
      Cons
        (Cons y94 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
        (tip2015sortMSortBU2Permutessmt2risers (Cons y223 xs57))
tip2015sortMSortBU2Permutessmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortMSortBU2Permutessmt2zisPermutation Nil y95 = null y95
tip2015sortMSortBU2Permutessmt2zisPermutation
  (Cons z101 xs58) y95 =
  (tip2015sortMSortBU2Permutessmt2zelem z101 y95) P.&&
    (tip2015sortMSortBU2Permutessmt2zisPermutation
       xs58 (tip2015sortMSortBU2Permutessmt2zdelete z101 y95))
tip2015sortMSortBU2Permutessmt2lmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2Permutessmt2lmerge Nil y96 = y96
tip2015sortMSortBU2Permutessmt2lmerge (Cons z102 x241) Nil =
  Cons z102 x241
tip2015sortMSortBU2Permutessmt2lmerge
  (Cons z102 x241) (Cons x322 x418) =
  case z102 P.<= x322 of
    P.True ->
      Cons
        z102 (tip2015sortMSortBU2Permutessmt2lmerge x241 (Cons x322 x418))
    P.False ->
      Cons
        x322 (tip2015sortMSortBU2Permutessmt2lmerge (Cons z102 x241) x418)
tip2015sortMSortBU2Permutessmt2pairwise ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list P.Int) ->
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBU2Permutessmt2pairwise Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBU2Permutessmt2pairwise (Cons xs59 Nil) =
  Cons
    xs59
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Grammarssimpexprunambig3smt2list P.Int))
tip2015sortMSortBU2Permutessmt2pairwise
  (Cons xs59 (Cons ys43 xss5)) =
  Cons
    (tip2015sortMSortBU2Permutessmt2lmerge xs59 ys43)
    (tip2015sortMSortBU2Permutessmt2pairwise xss5)
tip2015sortMSortBU2Permutessmt2mergingbu2 ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list P.Int) ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2Permutessmt2mergingbu2 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2Permutessmt2mergingbu2 (Cons xs60 Nil) = xs60
tip2015sortMSortBU2Permutessmt2mergingbu2
  (Cons xs60 (Cons z103 x242)) =
  tip2015sortMSortBU2Permutessmt2mergingbu2
    (tip2015sortMSortBU2Permutessmt2pairwise
       (Cons xs60 (Cons z103 x242)))
tip2015sortMSortBU2Permutessmt2msortbu2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2Permutessmt2msortbu2 x105 =
  tip2015sortMSortBU2Permutessmt2mergingbu2
    (tip2015sortMSortBU2Permutessmt2risers x105)
tip2015regexpReversesmt2rev ::
  Tip2015regexpRecPlussmt2R -> Tip2015regexpRecPlussmt2R
tip2015regexpReversesmt2rev x106 =
  case x106 of
    Tip2015regexpRecPlussmt2Plus a55 b14 ->
      Tip2015regexpRecPlussmt2Plus
        (tip2015regexpReversesmt2rev a55) (tip2015regexpReversesmt2rev b14)
    Tip2015regexpRecPlussmt2Seq c5 b23 ->
      Tip2015regexpRecPlussmt2Seq
        (tip2015regexpReversesmt2rev b23) (tip2015regexpReversesmt2rev c5)
    Tip2015regexpRecPlussmt2Star a210 ->
      Tip2015regexpRecPlussmt2Star (tip2015regexpReversesmt2rev a210)
    _ -> x106
tip2015sortMSortBUSortssmt2zisaplannerprop78smt2sorted ::
  Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortMSortBUSortssmt2zisaplannerprop78smt2sorted Nil = P.True
tip2015sortMSortBUSortssmt2zisaplannerprop78smt2sorted
  (Cons y97 Nil) =
  P.True
tip2015sortMSortBUSortssmt2zisaplannerprop78smt2sorted
  (Cons y97 (Cons y224 xs61)) =
  (y97 P.<= y224) P.&&
    (tip2015sortMSortBUSortssmt2zisaplannerprop78smt2sorted
       (Cons y224 xs61))
tip2015sortMSortBUSortssmt2lmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUSortssmt2lmerge Nil y98 = y98
tip2015sortMSortBUSortssmt2lmerge (Cons z104 x243) Nil =
  Cons z104 x243
tip2015sortMSortBUSortssmt2lmerge
  (Cons z104 x243) (Cons x323 x419) =
  case z104 P.<= x323 of
    P.True ->
      Cons z104 (tip2015sortMSortBUSortssmt2lmerge x243 (Cons x323 x419))
    P.False ->
      Cons x323 (tip2015sortMSortBUSortssmt2lmerge (Cons z104 x243) x419)
tip2015sortMSortBUSortssmt2pairwise ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list P.Int) ->
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBUSortssmt2pairwise Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBUSortssmt2pairwise (Cons xs62 Nil) =
  Cons
    xs62
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Grammarssimpexprunambig3smt2list P.Int))
tip2015sortMSortBUSortssmt2pairwise (Cons xs62 (Cons ys44 xss6)) =
  Cons
    (tip2015sortMSortBUSortssmt2lmerge xs62 ys44)
    (tip2015sortMSortBUSortssmt2pairwise xss6)
tip2015sortMSortBUSortssmt2mergingbu ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list P.Int) ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUSortssmt2mergingbu Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUSortssmt2mergingbu (Cons xs63 Nil) = xs63
tip2015sortMSortBUSortssmt2mergingbu (Cons xs63 (Cons z105 x244)) =
  tip2015sortMSortBUSortssmt2mergingbu
    (tip2015sortMSortBUSortssmt2pairwise (Cons xs63 (Cons z105 x244)))
tip2015sortMSortBUSortssmt2msortbu ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUSortssmt2msortbu x107 =
  tip2015sortMSortBUSortssmt2mergingbu
    (map2
       (\ y99 -> Cons y99 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
       x107)
tip2015bintimescommsmt2times :: Bin -> Bin -> Bin
tip2015bintimescommsmt2times Tip2015binplussmt2One y100 = y100
tip2015bintimescommsmt2times
  (Tip2015binplussmt2ZeroAnd xs64) y100 =
  Tip2015binplussmt2ZeroAnd (tip2015bintimescommsmt2times xs64 y100)
tip2015bintimescommsmt2times (Tip2015binplussmt2OneAnd ys45) y100 =
  tip2015binplussmt2plus
    (Tip2015binplussmt2ZeroAnd
       (tip2015bintimescommsmt2times ys45 y100))
    y100
toInteger ::
  Grammarssimpexprunambig5smt2T ->
    Isaplannerprop54smt2Nat -> Tip2015intaddassocsmt2Integer
toInteger TX y101 = Tip2015intaddassocsmt2P y101
toInteger TY Isaplannerprop54smt2Z =
  Tip2015intaddassocsmt2P Isaplannerprop54smt2Z
toInteger TY (Isaplannerprop54smt2S m6) =
  Tip2015intaddassocsmt2N m6
sign ::
  Tip2015intaddassocsmt2Integer -> Grammarssimpexprunambig5smt2T
sign (Tip2015intaddassocsmt2P y102) = TX
sign (Tip2015intaddassocsmt2N z106) = TY
opposite ::
  Grammarssimpexprunambig5smt2T -> Grammarssimpexprunambig5smt2T
opposite TX = TY
opposite TY = TX
timesSign ::
  Grammarssimpexprunambig5smt2T ->
    Grammarssimpexprunambig5smt2T -> Grammarssimpexprunambig5smt2T
timesSign TX y103 = y103
timesSign TY y103 = opposite y103
tip2015intmulidentrightsmt2one :: Tip2015intaddassocsmt2Integer
tip2015intmulidentrightsmt2one =
  Tip2015intaddassocsmt2P
    (Isaplannerprop54smt2S Isaplannerprop54smt2Z)
absVal :: Tip2015intaddassocsmt2Integer -> Isaplannerprop54smt2Nat
absVal (Tip2015intaddassocsmt2P n9) = n9
absVal (Tip2015intaddassocsmt2N m7) = Isaplannerprop54smt2S m7
tip2015intmulidentrightsmt2times ::
  Tip2015intaddassocsmt2Integer ->
    Tip2015intaddassocsmt2Integer -> Tip2015intaddassocsmt2Integer
tip2015intmulidentrightsmt2times x108 y104 =
  toInteger
    (timesSign (sign x108) (sign y104))
    (tip2015nataltmulsamesmt2mult (absVal x108) (absVal y104))
tip2015listSelectPermutationsticksmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015listSelectPermutationsticksmt2zcount x109 Nil =
  Isaplannerprop54smt2Z
tip2015listSelectPermutationsticksmt2zcount x109 (Cons z107 xs65) =
  case x109 P.== z107 of
    P.True ->
      Isaplannerprop54smt2S
        (tip2015listSelectPermutationsticksmt2zcount x109 xs65)
    P.False -> tip2015listSelectPermutationsticksmt2zcount x109 xs65
tip2015listSelectPermutationsticksmt2propSelectPermutations ::
  Grammarssimpexprunambig3smt2list
    (Isaplannerprop45smt2Pair
       P.Int (Grammarssimpexprunambig3smt2list P.Int)) ->
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015listSelectPermutationsticksmt2propSelectPermutations Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015listSelectPermutationsticksmt2propSelectPermutations
  (Cons (Pair2 y225 ys46) z108) =
  Cons
    (Cons y225 ys46)
    (tip2015listSelectPermutationsticksmt2propSelectPermutations z108)
tip2015sortMSortTDIsSortsmt2ztake ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a56 ->
      Grammarssimpexprunambig3smt2list a56
tip2015sortMSortTDIsSortsmt2ztake x110 y105 =
  case x110 P.== (0) of
    P.True -> Nil :: Grammarssimpexprunambig3smt2list a56
    P.False ->
      case y105 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a56
        Cons z109 xs66 ->
          Cons z109 (tip2015sortMSortTDIsSortsmt2ztake (x110 P.- (1)) xs66)
tip2015sortMSortTDIsSortsmt2zlength ::
  Grammarssimpexprunambig3smt2list a57 -> P.Int
tip2015sortMSortTDIsSortsmt2zlength Nil = 0
tip2015sortMSortTDIsSortsmt2zlength (Cons y106 xs67) =
  (1) P.+ (tip2015sortMSortTDIsSortsmt2zlength xs67)
tip2015sortMSortTDIsSortsmt2zdrop ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a58 ->
      Grammarssimpexprunambig3smt2list a58
tip2015sortMSortTDIsSortsmt2zdrop x111 y107 =
  case x111 P.== (0) of
    P.True -> y107
    P.False ->
      case y107 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a58
        Cons z110 xs112 ->
          tip2015sortMSortTDIsSortsmt2zdrop (x111 P.- (1)) xs112
tip2015sortMSortTDIsSortsmt2lmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortTDIsSortsmt2lmerge Nil y108 = y108
tip2015sortMSortTDIsSortsmt2lmerge (Cons z111 x245) Nil =
  Cons z111 x245
tip2015sortMSortTDIsSortsmt2lmerge
  (Cons z111 x245) (Cons x324 x420) =
  case z111 P.<= x324 of
    P.True ->
      Cons
        z111 (tip2015sortMSortTDIsSortsmt2lmerge x245 (Cons x324 x420))
    P.False ->
      Cons
        x324 (tip2015sortMSortTDIsSortsmt2lmerge (Cons z111 x245) x420)
tip2015sortMSortTDIsSortsmt2msorttd ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortTDIsSortsmt2msorttd Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortTDIsSortsmt2msorttd (Cons y109 Nil) =
  Cons y109 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortTDIsSortsmt2msorttd (Cons y109 (Cons x246 x325)) =
  let k2 =
        P.div
          (tip2015sortMSortTDIsSortsmt2zlength (Cons y109 (Cons x246 x325)))
          (2)
    in tip2015sortMSortTDIsSortsmt2lmerge
         (tip2015sortMSortTDIsSortsmt2msorttd
            (tip2015sortMSortTDIsSortsmt2ztake
               k2 (Cons y109 (Cons x246 x325))))
         (tip2015sortMSortTDIsSortsmt2msorttd
            (tip2015sortMSortTDIsSortsmt2zdrop
               k2 (Cons y109 (Cons x246 x325))))
tip2015sortMSortTDIsSortsmt2insert2 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortTDIsSortsmt2insert2 x112 Nil =
  Cons x112 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortTDIsSortsmt2insert2 x112 (Cons z112 xs68) =
  case x112 P.<= z112 of
    P.True -> Cons x112 (Cons z112 xs68)
    P.False ->
      Cons z112 (tip2015sortMSortTDIsSortsmt2insert2 x112 xs68)
tip2015sortMSortTDIsSortsmt2isort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortTDIsSortsmt2isort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortTDIsSortsmt2isort (Cons y110 xs69) =
  tip2015sortMSortTDIsSortsmt2insert2
    y110 (tip2015sortMSortTDIsSortsmt2isort xs69)
tip2015sortNMSortTDIsSortsmt2lmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortNMSortTDIsSortsmt2lmerge Nil y111 = y111
tip2015sortNMSortTDIsSortsmt2lmerge (Cons z113 x247) Nil =
  Cons z113 x247
tip2015sortNMSortTDIsSortsmt2lmerge
  (Cons z113 x247) (Cons x326 x421) =
  case z113 P.<= x326 of
    P.True ->
      Cons
        z113 (tip2015sortNMSortTDIsSortsmt2lmerge x247 (Cons x326 x421))
    P.False ->
      Cons
        x326 (tip2015sortNMSortTDIsSortsmt2lmerge (Cons z113 x247) x421)
tip2015sortNMSortTDIsSortsmt2insert2 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortNMSortTDIsSortsmt2insert2 x113 Nil =
  Cons x113 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortNMSortTDIsSortsmt2insert2 x113 (Cons z114 xs70) =
  case x113 P.<= z114 of
    P.True -> Cons x113 (Cons z114 xs70)
    P.False ->
      Cons z114 (tip2015sortNMSortTDIsSortsmt2insert2 x113 xs70)
tip2015sortNMSortTDIsSortsmt2isort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNMSortTDIsSortsmt2isort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNMSortTDIsSortsmt2isort (Cons y112 xs71) =
  tip2015sortNMSortTDIsSortsmt2insert2
    y112 (tip2015sortNMSortTDIsSortsmt2isort xs71)
half :: Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
half Isaplannerprop54smt2Z = Isaplannerprop54smt2Z
half (Isaplannerprop54smt2S Isaplannerprop54smt2Z) =
  Isaplannerprop54smt2Z
half (Isaplannerprop54smt2S (Isaplannerprop54smt2S n10)) =
  Isaplannerprop54smt2S (half n10)
tip2015sortNMSortTDIsSortsmt2nmsorttd ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNMSortTDIsSortsmt2nmsorttd Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNMSortTDIsSortsmt2nmsorttd (Cons y113 Nil) =
  Cons y113 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortNMSortTDIsSortsmt2nmsorttd
  (Cons y113 (Cons x248 x327)) =
  let k3 =
        half (isaplannerprop68smt2len (Cons y113 (Cons x248 x327)))
    in tip2015sortNMSortTDIsSortsmt2lmerge
         (tip2015sortNMSortTDIsSortsmt2nmsorttd
            (isaplannerprop82smt2take k3 (Cons y113 (Cons x248 x327))))
         (tip2015sortNMSortTDIsSortsmt2nmsorttd
            (isaplannerprop12smt2drop k3 (Cons y113 (Cons x248 x327))))
isSpecial :: Token -> P.Bool
isSpecial x114 =
  case x114 of
    ESC -> P.True
    Tip2015escapeNoSpecialsmt2P -> P.True
    Tip2015escapeNoSpecialsmt2Q -> P.True
    Tip2015escapeNoSpecialsmt2R -> P.True
    _ -> P.False
isEsc :: Token -> P.Bool
isEsc x115 =
  case x115 of
    ESC -> P.True
    _ -> P.False
tip2015escapeNoSpecialsmt2ok :: Token -> P.Bool
tip2015escapeNoSpecialsmt2ok x116 =
  (P.not (isSpecial x116)) P.|| (isEsc x116)
code :: Token -> Token
code x117 =
  case x117 of
    ESC -> ESC
    Tip2015escapeNoSpecialsmt2P -> Tip2015escapeNoSpecialsmt2A
    Tip2015escapeNoSpecialsmt2Q -> Tip2015escapeNoSpecialsmt2B
    Tip2015escapeNoSpecialsmt2R -> Tip2015escapeNoSpecialsmt2C
    _ -> x117
tip2015escapeNoSpecialsmt2escape ::
  Grammarssimpexprunambig3smt2list Token ->
    Grammarssimpexprunambig3smt2list Token
tip2015escapeNoSpecialsmt2escape Nil =
  Nil :: Grammarssimpexprunambig3smt2list Token
tip2015escapeNoSpecialsmt2escape (Cons y114 xs72) =
  case isSpecial y114 of
    P.True ->
      Cons ESC (Cons (code y114) (tip2015escapeNoSpecialsmt2escape xs72))
    P.False -> Cons y114 (tip2015escapeNoSpecialsmt2escape xs72)
tip2015sortBSortCountsmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015sortBSortCountsmt2zcount x118 Nil = Isaplannerprop54smt2Z
tip2015sortBSortCountsmt2zcount x118 (Cons z115 xs73) =
  case x118 P.== z115 of
    P.True ->
      Isaplannerprop54smt2S (tip2015sortBSortCountsmt2zcount x118 xs73)
    P.False -> tip2015sortBSortCountsmt2zcount x118 xs73
tip2015sortBSortCountsmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortCountsmt2sort2 x119 y115 =
  case x119 P.<= y115 of
    P.True ->
      Cons
        x119 (Cons y115 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y115 (Cons x119 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortBSortCountsmt2evens ::
  Grammarssimpexprunambig3smt2list a59 ->
    Grammarssimpexprunambig3smt2list a59
tip2015sortBSortCountsmt2evens Nil =
  Nil :: Grammarssimpexprunambig3smt2list a59
tip2015sortBSortCountsmt2evens (Cons y116 xs74) =
  Cons y116 (tip2015sortBSortCountsmt2odds xs74)
tip2015sortBSortCountsmt2odds ::
  Grammarssimpexprunambig3smt2list a60 ->
    Grammarssimpexprunambig3smt2list a60
tip2015sortBSortCountsmt2odds Nil =
  Nil :: Grammarssimpexprunambig3smt2list a60
tip2015sortBSortCountsmt2odds (Cons y117 xs75) =
  tip2015sortBSortCountsmt2evens xs75
tip2015sortBSortCountsmt2pairs ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortCountsmt2pairs Nil y118 = y118
tip2015sortBSortCountsmt2pairs (Cons z116 x249) Nil =
  Cons z116 x249
tip2015sortBSortCountsmt2pairs (Cons z116 x249) (Cons x328 x422) =
  append
    (tip2015sortBSortCountsmt2sort2 z116 x328)
    (tip2015sortBSortCountsmt2pairs x249 x422)
tip2015sortBSortCountsmt2stitch ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortCountsmt2stitch Nil y119 = y119
tip2015sortBSortCountsmt2stitch (Cons z117 xs76) y119 =
  Cons z117 (tip2015sortBSortCountsmt2pairs xs76 y119)
tip2015sortBSortCountsmt2bmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortCountsmt2bmerge Nil y120 =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortCountsmt2bmerge (Cons z118 x250) Nil =
  Cons z118 x250
tip2015sortBSortCountsmt2bmerge (Cons z118 Nil) (Cons x329 Nil) =
  tip2015sortBSortCountsmt2sort2 z118 x329
tip2015sortBSortCountsmt2bmerge
  (Cons z118 Nil) (Cons x329 (Cons x511 x611)) =
  tip2015sortBSortCountsmt2stitch
    (tip2015sortBSortCountsmt2bmerge
       (tip2015sortBSortCountsmt2evens
          (Cons z118 (Nil :: Grammarssimpexprunambig3smt2list P.Int)))
       (tip2015sortBSortCountsmt2evens (Cons x329 (Cons x511 x611))))
    (tip2015sortBSortCountsmt2bmerge
       (tip2015sortBSortCountsmt2odds
          (Cons z118 (Nil :: Grammarssimpexprunambig3smt2list P.Int)))
       (tip2015sortBSortCountsmt2odds (Cons x329 (Cons x511 x611))))
tip2015sortBSortCountsmt2bmerge
  (Cons z118 (Cons x710 x810)) (Cons x329 x423) =
  tip2015sortBSortCountsmt2stitch
    (tip2015sortBSortCountsmt2bmerge
       (tip2015sortBSortCountsmt2evens (Cons z118 (Cons x710 x810)))
       (tip2015sortBSortCountsmt2evens (Cons x329 x423)))
    (tip2015sortBSortCountsmt2bmerge
       (tip2015sortBSortCountsmt2odds (Cons z118 (Cons x710 x810)))
       (tip2015sortBSortCountsmt2odds (Cons x329 x423)))
tip2015sortBSortCountsmt2bsort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortCountsmt2bsort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortCountsmt2bsort (Cons y121 Nil) =
  Cons y121 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortBSortCountsmt2bsort (Cons y121 (Cons x251 x330)) =
  tip2015sortBSortCountsmt2bmerge
    (tip2015sortBSortCountsmt2bsort
       (tip2015sortBSortCountsmt2evens (Cons y121 (Cons x251 x330))))
    (tip2015sortBSortCountsmt2bsort
       (tip2015sortBSortCountsmt2odds (Cons y121 (Cons x251 x330))))
tip2015sortTSortIsSortsmt2insert2 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortTSortIsSortsmt2insert2 x120 Nil =
  Cons x120 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortTSortIsSortsmt2insert2 x120 (Cons z119 xs77) =
  case x120 P.<= z119 of
    P.True -> Cons x120 (Cons z119 xs77)
    P.False -> Cons z119 (tip2015sortTSortIsSortsmt2insert2 x120 xs77)
tip2015sortTSortIsSortsmt2isort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortTSortIsSortsmt2isort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortTSortIsSortsmt2isort (Cons y122 xs78) =
  tip2015sortTSortIsSortsmt2insert2
    y122 (tip2015sortTSortIsSortsmt2isort xs78)
tip2015sortTSortIsSortsmt2add ::
  P.Int ->
    Tip2015treesortAddSamesmt2Tree P.Int ->
      Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortTSortIsSortsmt2add
  x121 (Tip2015treesortAddSamesmt2Node p7 z120 q9) =
  case x121 P.<= z120 of
    P.True ->
      Tip2015treesortAddSamesmt2Node
        (tip2015sortTSortIsSortsmt2add x121 p7) z120 q9
    P.False ->
      Tip2015treesortAddSamesmt2Node
        p7 z120 (tip2015sortTSortIsSortsmt2add x121 q9)
tip2015sortTSortIsSortsmt2add x121 Tip2015treesortAddSamesmt2Nil =
  Tip2015treesortAddSamesmt2Node
    (Tip2015treesortAddSamesmt2Nil ::
       Tip2015treesortAddSamesmt2Tree P.Int)
    x121
    (Tip2015treesortAddSamesmt2Nil ::
       Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortTSortIsSortsmt2toTree ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortTSortIsSortsmt2toTree Nil =
  Tip2015treesortAddSamesmt2Nil ::
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortTSortIsSortsmt2toTree (Cons y123 xs79) =
  tip2015sortTSortIsSortsmt2add
    y123 (tip2015sortTSortIsSortsmt2toTree xs79)
tip2015sortTSortIsSortsmt2tsort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortTSortIsSortsmt2tsort x122 =
  tip2015treesortAddSamesmt2flatten
    (tip2015sortTSortIsSortsmt2toTree x122)
    (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortStoogeSort2IsSortsmt2ztake ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a61 ->
      Grammarssimpexprunambig3smt2list a61
tip2015sortStoogeSort2IsSortsmt2ztake x123 y124 =
  case x123 P.== (0) of
    P.True -> Nil :: Grammarssimpexprunambig3smt2list a61
    P.False ->
      case y124 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a61
        Cons z121 xs80 ->
          Cons
            z121 (tip2015sortStoogeSort2IsSortsmt2ztake (x123 P.- (1)) xs80)
tip2015sortStoogeSort2IsSortsmt2zlength ::
  Grammarssimpexprunambig3smt2list a62 -> P.Int
tip2015sortStoogeSort2IsSortsmt2zlength Nil = 0
tip2015sortStoogeSort2IsSortsmt2zlength (Cons y125 xs81) =
  (1) P.+ (tip2015sortStoogeSort2IsSortsmt2zlength xs81)
tip2015sortStoogeSort2IsSortsmt2zdrop ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a63 ->
      Grammarssimpexprunambig3smt2list a63
tip2015sortStoogeSort2IsSortsmt2zdrop x124 y126 =
  case x124 P.== (0) of
    P.True -> y126
    P.False ->
      case y126 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a63
        Cons z122 xs113 ->
          tip2015sortStoogeSort2IsSortsmt2zdrop (x124 P.- (1)) xs113
tip2015sortStoogeSort2IsSortsmt2zsplitAt ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a64 ->
      Isaplannerprop45smt2Pair
        (Grammarssimpexprunambig3smt2list a64)
        (Grammarssimpexprunambig3smt2list a64)
tip2015sortStoogeSort2IsSortsmt2zsplitAt x125 y127 =
  Pair2
    (tip2015sortStoogeSort2IsSortsmt2ztake x125 y127)
    (tip2015sortStoogeSort2IsSortsmt2zdrop x125 y127)
tip2015sortStoogeSort2IsSortsmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSort2IsSortsmt2sort2 x126 y128 =
  case x126 P.<= y128 of
    P.True ->
      Cons
        x126 (Cons y128 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y128 (Cons x126 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortStoogeSort2IsSortsmt2insert2 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSort2IsSortsmt2insert2 x127 Nil =
  Cons x127 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortStoogeSort2IsSortsmt2insert2 x127 (Cons z123 xs82) =
  case x127 P.<= z123 of
    P.True -> Cons x127 (Cons z123 xs82)
    P.False ->
      Cons z123 (tip2015sortStoogeSort2IsSortsmt2insert2 x127 xs82)
tip2015sortStoogeSort2IsSortsmt2isort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSort2IsSortsmt2isort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSort2IsSortsmt2isort (Cons y129 xs83) =
  tip2015sortStoogeSort2IsSortsmt2insert2
    y129 (tip2015sortStoogeSort2IsSortsmt2isort xs83)
mergeLists ::
  Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
      Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
mergeLists Nil y130 = y130
mergeLists (Cons z124 x252) Nil = Cons z124 x252
mergeLists (Cons z124 x252) (Cons x331 x424) =
  case isaplannerprop68smt2le z124 x331 of
    P.True -> Cons z124 (mergeLists x252 (Cons x331 x424))
    P.False -> Cons x331 (mergeLists (Cons z124 x252) x424)
heap1 ::
  Isaplannerprop54smt2Nat ->
    Tip2015heapSortPermutessmt2Heap -> P.Bool
heap1 x128 (Tip2015heapSortPermutessmt2Node l4 z125 r4) =
  (isaplannerprop68smt2le x128 z125) P.&&
    ((heap1 z125 l4) P.&& (heap1 z125 r4))
heap1 x128 Tip2015heapSortPermutessmt2Nil = P.True
tip2015heapmergesmt2heap ::
  Tip2015heapSortPermutessmt2Heap -> P.Bool
tip2015heapmergesmt2heap
  (Tip2015heapSortPermutessmt2Node l5 y131 r5) =
  (heap1 y131 l5) P.&& (heap1 y131 r5)
tip2015heapmergesmt2heap Tip2015heapSortPermutessmt2Nil = P.True
tip2015sortNStoogeSortCountsmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015sortNStoogeSortCountsmt2zcount x129 Nil =
  Isaplannerprop54smt2Z
tip2015sortNStoogeSortCountsmt2zcount x129 (Cons z126 xs84) =
  case x129 P.== z126 of
    P.True ->
      Isaplannerprop54smt2S
        (tip2015sortNStoogeSortCountsmt2zcount x129 xs84)
    P.False -> tip2015sortNStoogeSortCountsmt2zcount x129 xs84
tip2015sortNStoogeSortCountsmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortCountsmt2sort2 x130 y132 =
  case x130 P.<= y132 of
    P.True ->
      Cons
        x130 (Cons y132 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y132 (Cons x130 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortNStoogeSortCountsmt2nstooge1sort2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortCountsmt2nstooge1sort2 x131 =
  case tip2015sortNStoogeSort2Countsmt2splitAt
         (third (isaplannerprop68smt2len x131))
         (isaplannerprop85smt2rev x131) of
    Pair2 ys47 zs6 ->
      append
        (tip2015sortNStoogeSortCountsmt2nstoogesort zs6)
        (isaplannerprop85smt2rev ys47)
tip2015sortNStoogeSortCountsmt2nstoogesort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortCountsmt2nstoogesort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortCountsmt2nstoogesort (Cons y133 Nil) =
  Cons y133 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortNStoogeSortCountsmt2nstoogesort
  (Cons y133 (Cons y226 Nil)) =
  tip2015sortNStoogeSortCountsmt2sort2 y133 y226
tip2015sortNStoogeSortCountsmt2nstoogesort
  (Cons y133 (Cons y226 (Cons x332 x425))) =
  tip2015sortNStoogeSortCountsmt2nstooge1sort2
    (tip2015sortNStoogeSortCountsmt2nstooge1sort1
       (tip2015sortNStoogeSortCountsmt2nstooge1sort2
          (Cons y133 (Cons y226 (Cons x332 x425)))))
tip2015sortNStoogeSortCountsmt2nstooge1sort1 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortCountsmt2nstooge1sort1 x132 =
  case tip2015sortNStoogeSort2Countsmt2splitAt
         (third (isaplannerprop68smt2len x132)) x132 of
    Pair2 ys48 zs7 ->
      append ys48 (tip2015sortNStoogeSortCountsmt2nstoogesort zs7)
tip2015listznubnubsmt2zdeleteAll ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015listznubnubsmt2zdeleteAll x133 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015listznubnubsmt2zdeleteAll x133 (Cons z127 xs85) =
  case x133 P.== z127 of
    P.True -> tip2015listznubnubsmt2zdeleteAll x133 xs85
    P.False -> Cons z127 (tip2015listznubnubsmt2zdeleteAll x133 xs85)
tip2015listznubnubsmt2znub ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015listznubnubsmt2znub Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015listznubnubsmt2znub (Cons y134 xs86) =
  Cons
    y134
    (tip2015listznubnubsmt2zdeleteAll
       y134 (tip2015listznubnubsmt2znub xs86))
unequal ::
  Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat -> P.Bool
unequal x134 y135 = P.not (isaplannerprop37smt2equal x134 y135)
tip2015sortMSortBUPermutessmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortMSortBUPermutessmt2zelem x135 Nil = P.False
tip2015sortMSortBUPermutessmt2zelem x135 (Cons z128 ys49) =
  (x135 P.== z128) P.||
    (tip2015sortMSortBUPermutessmt2zelem x135 ys49)
tip2015sortMSortBUPermutessmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUPermutessmt2zdelete x136 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUPermutessmt2zdelete x136 (Cons z129 ys50) =
  case x136 P.== z129 of
    P.True -> ys50
    P.False ->
      Cons z129 (tip2015sortMSortBUPermutessmt2zdelete x136 ys50)
tip2015sortMSortBUPermutessmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortMSortBUPermutessmt2zisPermutation Nil y136 = null y136
tip2015sortMSortBUPermutessmt2zisPermutation
  (Cons z130 xs87) y136 =
  (tip2015sortMSortBUPermutessmt2zelem z130 y136) P.&&
    (tip2015sortMSortBUPermutessmt2zisPermutation
       xs87 (tip2015sortMSortBUPermutessmt2zdelete z130 y136))
tip2015sortMSortBUPermutessmt2lmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUPermutessmt2lmerge Nil y137 = y137
tip2015sortMSortBUPermutessmt2lmerge (Cons z131 x253) Nil =
  Cons z131 x253
tip2015sortMSortBUPermutessmt2lmerge
  (Cons z131 x253) (Cons x333 x426) =
  case z131 P.<= x333 of
    P.True ->
      Cons
        z131 (tip2015sortMSortBUPermutessmt2lmerge x253 (Cons x333 x426))
    P.False ->
      Cons
        x333 (tip2015sortMSortBUPermutessmt2lmerge (Cons z131 x253) x426)
tip2015sortMSortBUPermutessmt2pairwise ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list P.Int) ->
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBUPermutessmt2pairwise Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBUPermutessmt2pairwise (Cons xs88 Nil) =
  Cons
    xs88
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Grammarssimpexprunambig3smt2list P.Int))
tip2015sortMSortBUPermutessmt2pairwise
  (Cons xs88 (Cons ys51 xss7)) =
  Cons
    (tip2015sortMSortBUPermutessmt2lmerge xs88 ys51)
    (tip2015sortMSortBUPermutessmt2pairwise xss7)
tip2015sortMSortBUPermutessmt2mergingbu ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list P.Int) ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUPermutessmt2mergingbu Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUPermutessmt2mergingbu (Cons xs89 Nil) = xs89
tip2015sortMSortBUPermutessmt2mergingbu
  (Cons xs89 (Cons z132 x254)) =
  tip2015sortMSortBUPermutessmt2mergingbu
    (tip2015sortMSortBUPermutessmt2pairwise
       (Cons xs89 (Cons z132 x254)))
tip2015sortMSortBUPermutessmt2msortbu ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBUPermutessmt2msortbu x137 =
  tip2015sortMSortBUPermutessmt2mergingbu
    (map2
       (\ y138 ->
          Cons y138 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
       x137)
tip2015sortNStoogeSort2Sortssmt2zisaplannerprop78smt2sorted ::
  Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortNStoogeSort2Sortssmt2zisaplannerprop78smt2sorted Nil =
  P.True
tip2015sortNStoogeSort2Sortssmt2zisaplannerprop78smt2sorted
  (Cons y139 Nil) =
  P.True
tip2015sortNStoogeSort2Sortssmt2zisaplannerprop78smt2sorted
  (Cons y139 (Cons y227 xs90)) =
  (y139 P.<= y227) P.&&
    (tip2015sortNStoogeSort2Sortssmt2zisaplannerprop78smt2sorted
       (Cons y227 xs90))
tip2015sortNStoogeSort2Sortssmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2Sortssmt2sort2 x138 y140 =
  case x138 P.<= y140 of
    P.True ->
      Cons
        x138 (Cons y140 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y140 (Cons x138 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortNStoogeSort2Sortssmt2nstooge2sort2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2Sortssmt2nstooge2sort2 x139 =
  case tip2015sortNStoogeSort2Countsmt2splitAt
         (twoThirds (isaplannerprop68smt2len x139)) x139 of
    Pair2 ys52 zs8 ->
      append (tip2015sortNStoogeSort2Sortssmt2nstoogesort2 ys52) zs8
tip2015sortNStoogeSort2Sortssmt2nstoogesort2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2Sortssmt2nstoogesort2 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2Sortssmt2nstoogesort2 (Cons y141 Nil) =
  Cons y141 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortNStoogeSort2Sortssmt2nstoogesort2
  (Cons y141 (Cons y228 Nil)) =
  tip2015sortNStoogeSort2Sortssmt2sort2 y141 y228
tip2015sortNStoogeSort2Sortssmt2nstoogesort2
  (Cons y141 (Cons y228 (Cons x334 x427))) =
  tip2015sortNStoogeSort2Sortssmt2nstooge2sort2
    (tip2015sortNStoogeSort2Sortssmt2nstooge2sort1
       (tip2015sortNStoogeSort2Sortssmt2nstooge2sort2
          (Cons y141 (Cons y228 (Cons x334 x427)))))
tip2015sortNStoogeSort2Sortssmt2nstooge2sort1 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2Sortssmt2nstooge2sort1 x140 =
  case tip2015sortNStoogeSort2Countsmt2splitAt
         (third (isaplannerprop68smt2len x140)) x140 of
    Pair2 ys53 zs9 ->
      append ys53 (tip2015sortNStoogeSort2Sortssmt2nstoogesort2 zs9)
tip2015relaxedprefixisprefix1smt2eq ::
  GrammarspackratunambigPackratsmt2Tok ->
    GrammarspackratunambigPackratsmt2Tok -> P.Bool
tip2015relaxedprefixisprefix1smt2eq
  GrammarspackratunambigPackratsmt2X y142 =
  case y142 of
    GrammarspackratunambigPackratsmt2X -> P.True
    _ -> P.False
tip2015relaxedprefixisprefix1smt2eq
  GrammarspackratunambigPackratsmt2Y y142 =
  case y142 of
    GrammarspackratunambigPackratsmt2Y -> P.True
    _ -> P.False
tip2015relaxedprefixisprefix1smt2eq
  GrammarspackratunambigPackratsmt2Z y142 =
  case y142 of
    GrammarspackratunambigPackratsmt2Z -> P.True
    _ -> P.False
isPrefix ::
  Grammarssimpexprunambig3smt2list
    GrammarspackratunambigPackratsmt2Tok ->
    Grammarssimpexprunambig3smt2list
      GrammarspackratunambigPackratsmt2Tok ->
      P.Bool
isPrefix Nil y143 = P.True
isPrefix (Cons z133 x255) Nil = P.False
isPrefix (Cons z133 x255) (Cons x335 x428) =
  (tip2015relaxedprefixisprefix1smt2eq z133 x335) P.&&
    (isPrefix x255 x428)
isRelaxedPrefix ::
  Grammarssimpexprunambig3smt2list
    GrammarspackratunambigPackratsmt2Tok ->
    Grammarssimpexprunambig3smt2list
      GrammarspackratunambigPackratsmt2Tok ->
      P.Bool
isRelaxedPrefix Nil y144 = P.True
isRelaxedPrefix (Cons z134 Nil) y144 = P.True
isRelaxedPrefix (Cons z134 (Cons x336 x429)) Nil = P.False
isRelaxedPrefix (Cons z134 (Cons x336 x429)) (Cons x512 x612) =
  case tip2015relaxedprefixisprefix1smt2eq z134 x512 of
    P.True -> isRelaxedPrefix (Cons x336 x429) x612
    P.False -> isPrefix (Cons x336 x429) (Cons x512 x612)
tip2015sortBubSortCountsmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015sortBubSortCountsmt2zcount x141 Nil = Isaplannerprop54smt2Z
tip2015sortBubSortCountsmt2zcount x141 (Cons z135 xs91) =
  case x141 P.== z135 of
    P.True ->
      Isaplannerprop54smt2S (tip2015sortBubSortCountsmt2zcount x141 xs91)
    P.False -> tip2015sortBubSortCountsmt2zcount x141 xs91
tip2015sortBubSortCountsmt2bubble ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Isaplannerprop45smt2Pair
      P.Bool (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortBubSortCountsmt2bubble Nil =
  Pair2 P.False (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortBubSortCountsmt2bubble (Cons y145 Nil) =
  Pair2
    P.False (Cons y145 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortBubSortCountsmt2bubble (Cons y145 (Cons y229 xs92)) =
  case y145 P.<= y229 of
    P.True ->
      case tip2015sortBubSortCountsmt2bubble (Cons y229 xs92) of
        Pair2 b24 zs10 -> Pair2 b24 (Cons y145 zs10)
    P.False ->
      case tip2015sortBubSortCountsmt2bubble (Cons y145 xs92) of
        Pair2 c6 ys54 -> Pair2 P.True (Cons y229 ys54)
tip2015sortBubSortCountsmt2bubsort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortBubSortCountsmt2bubsort x142 =
  case tip2015sortBubSortCountsmt2bubble x142 of
    Pair2 c7 ys55 ->
      case c7 of
        P.True -> tip2015sortBubSortCountsmt2bubsort ys55
        P.False -> x142
tip2015sortNStoogeSort2Permutessmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortNStoogeSort2Permutessmt2zelem x143 Nil = P.False
tip2015sortNStoogeSort2Permutessmt2zelem x143 (Cons z136 ys56) =
  (x143 P.== z136) P.||
    (tip2015sortNStoogeSort2Permutessmt2zelem x143 ys56)
tip2015sortNStoogeSort2Permutessmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2Permutessmt2zdelete x144 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2Permutessmt2zdelete x144 (Cons z137 ys57) =
  case x144 P.== z137 of
    P.True -> ys57
    P.False ->
      Cons z137 (tip2015sortNStoogeSort2Permutessmt2zdelete x144 ys57)
tip2015sortNStoogeSort2Permutessmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2Permutessmt2sort2 x145 y146 =
  case x145 P.<= y146 of
    P.True ->
      Cons
        x145 (Cons y146 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y146 (Cons x145 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortNStoogeSort2Permutessmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortNStoogeSort2Permutessmt2zisPermutation Nil y147 =
  null y147
tip2015sortNStoogeSort2Permutessmt2zisPermutation
  (Cons z138 xs93) y147 =
  (tip2015sortNStoogeSort2Permutessmt2zelem z138 y147) P.&&
    (tip2015sortNStoogeSort2Permutessmt2zisPermutation
       xs93 (tip2015sortNStoogeSort2Permutessmt2zdelete z138 y147))
tip2015sortNStoogeSort2Permutessmt2nstooge2sort2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2Permutessmt2nstooge2sort2 x146 =
  case tip2015sortNStoogeSort2Countsmt2splitAt
         (twoThirds (isaplannerprop68smt2len x146)) x146 of
    Pair2 ys58 zs11 ->
      append (tip2015sortNStoogeSort2Permutessmt2nstoogesort2 ys58) zs11
tip2015sortNStoogeSort2Permutessmt2nstoogesort2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2Permutessmt2nstoogesort2 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2Permutessmt2nstoogesort2 (Cons y148 Nil) =
  Cons y148 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortNStoogeSort2Permutessmt2nstoogesort2
  (Cons y148 (Cons y230 Nil)) =
  tip2015sortNStoogeSort2Permutessmt2sort2 y148 y230
tip2015sortNStoogeSort2Permutessmt2nstoogesort2
  (Cons y148 (Cons y230 (Cons x337 x430))) =
  tip2015sortNStoogeSort2Permutessmt2nstooge2sort2
    (tip2015sortNStoogeSort2Permutessmt2nstooge2sort1
       (tip2015sortNStoogeSort2Permutessmt2nstooge2sort2
          (Cons y148 (Cons y230 (Cons x337 x430)))))
tip2015sortNStoogeSort2Permutessmt2nstooge2sort1 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2Permutessmt2nstooge2sort1 x147 =
  case tip2015sortNStoogeSort2Countsmt2splitAt
         (third (isaplannerprop68smt2len x147)) x147 of
    Pair2 ys59 zs12 ->
      append ys59 (tip2015sortNStoogeSort2Permutessmt2nstoogesort2 zs12)
tip2015propositionalOkaysmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015propositionalOkaysmt2zelem x148 Nil = P.False
tip2015propositionalOkaysmt2zelem x148 (Cons z139 ys60) =
  (x148 P.== z139) P.|| (tip2015propositionalOkaysmt2zelem x148 ys60)
tip2015propositionalOkaysmt2models4 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list
      (Isaplannerprop45smt2Pair P.Int P.Bool) ->
      Grammarssimpexprunambig3smt2list P.Bool
tip2015propositionalOkaysmt2models4 x149 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Bool
tip2015propositionalOkaysmt2models4
  x149 (Cons (Pair2 y231 P.True) x256) =
  tip2015propositionalOkaysmt2models4 x149 x256
tip2015propositionalOkaysmt2models4
  x149 (Cons (Pair2 y231 P.False) x256) =
  Cons
    (x149 P.== y231) (tip2015propositionalOkaysmt2models4 x149 x256)
tip2015propositionalOkaysmt2models3 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list
      (Isaplannerprop45smt2Pair P.Int P.Bool) ->
      Grammarssimpexprunambig3smt2list P.Bool
tip2015propositionalOkaysmt2models3 x150 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Bool
tip2015propositionalOkaysmt2models3
  x150 (Cons (Pair2 y232 P.True) x257) =
  Cons
    (x150 P.== y232) (tip2015propositionalOkaysmt2models3 x150 x257)
tip2015propositionalOkaysmt2models3
  x150 (Cons (Pair2 y232 P.False) x257) =
  tip2015propositionalOkaysmt2models3 x150 x257
okay ::
  Grammarssimpexprunambig3smt2list
    (Isaplannerprop45smt2Pair P.Int P.Bool) ->
    P.Bool
okay Nil = P.True
okay (Cons (Pair2 z140 c8) m8) =
  (P.not
     (tip2015propositionalOkaysmt2zelem
        z140 (map2 (\ x258 -> fst x258) m8))) P.&&
    (okay m8)
split2 ::
  a65 ->
    Grammarssimpexprunambig3smt2list
      (Isaplannerprop45smt2Pair
         (Grammarssimpexprunambig3smt2list a65)
         (Grammarssimpexprunambig3smt2list a65)) ->
      Grammarssimpexprunambig3smt2list
        (Isaplannerprop45smt2Pair
           (Grammarssimpexprunambig3smt2list a65)
           (Grammarssimpexprunambig3smt2list a65))
split2 x151 Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Isaplannerprop45smt2Pair
         (Grammarssimpexprunambig3smt2list a65)
         (Grammarssimpexprunambig3smt2list a65))
split2 x151 (Cons (Pair2 xs94 ys61) x259) =
  Cons (Pair2 (Cons x151 xs94) ys61) (split2 x151 x259)
tip2015regexpRecSeqsmt2split ::
  Grammarssimpexprunambig3smt2list a66 ->
    Grammarssimpexprunambig3smt2list
      (Isaplannerprop45smt2Pair
         (Grammarssimpexprunambig3smt2list a66)
         (Grammarssimpexprunambig3smt2list a66))
tip2015regexpRecSeqsmt2split Nil =
  Cons
    (Pair2
       (Nil :: Grammarssimpexprunambig3smt2list a66)
       (Nil :: Grammarssimpexprunambig3smt2list a66))
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Isaplannerprop45smt2Pair
            (Grammarssimpexprunambig3smt2list a66)
            (Grammarssimpexprunambig3smt2list a66)))
tip2015regexpRecSeqsmt2split (Cons y149 s2) =
  Cons
    (Pair2
       (Nil :: Grammarssimpexprunambig3smt2list a66) (Cons y149 s2))
    (split2 y149 (tip2015regexpRecSeqsmt2split s2))
propRecSeq ::
  Tip2015regexpRecPlussmt2R ->
    Tip2015regexpRecPlussmt2R ->
      Grammarssimpexprunambig3smt2list
        (Isaplannerprop45smt2Pair
           (Grammarssimpexprunambig3smt2list Grammarssimpexprunambig5smt2T)
           (Grammarssimpexprunambig3smt2list
              Grammarssimpexprunambig5smt2T)) ->
        Grammarssimpexprunambig3smt2list P.Bool
propRecSeq p8 q10 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Bool
propRecSeq p8 q10 (Cons (Pair2 s1 s22) z141) =
  Cons
    ((recognise p8 s1) P.&& (recognise q10 s22))
    (propRecSeq p8 q10 z141)
tip2015sortSSortPermutessmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortSSortPermutessmt2zelem x152 Nil = P.False
tip2015sortSSortPermutessmt2zelem x152 (Cons z142 ys62) =
  (x152 P.== z142) P.|| (tip2015sortSSortPermutessmt2zelem x152 ys62)
tip2015sortSSortPermutessmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortPermutessmt2zdelete x153 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortPermutessmt2zdelete x153 (Cons z143 ys63) =
  case x153 P.== z143 of
    P.True -> ys63
    P.False ->
      Cons z143 (tip2015sortSSortPermutessmt2zdelete x153 ys63)
tip2015sortSSortPermutessmt2ssortminimum ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Int
tip2015sortSSortPermutessmt2ssortminimum x154 Nil = x154
tip2015sortSSortPermutessmt2ssortminimum x154 (Cons z144 ys64) =
  case z144 P.<= x154 of
    P.True -> tip2015sortSSortPermutessmt2ssortminimum z144 ys64
    P.False -> tip2015sortSSortPermutessmt2ssortminimum x154 ys64
tip2015sortSSortPermutessmt2ssort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortPermutessmt2ssort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortPermutessmt2ssort (Cons y150 ys65) =
  let m9 = tip2015sortSSortPermutessmt2ssortminimum y150 ys65
    in Cons
         m9
         (tip2015sortSSortPermutessmt2ssort
            (tip2015sortSSortPermutessmt2zdelete m9 (Cons y150 ys65)))
tip2015sortSSortPermutessmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortSSortPermutessmt2zisPermutation Nil y151 = null y151
tip2015sortSSortPermutessmt2zisPermutation (Cons z145 xs95) y151 =
  (tip2015sortSSortPermutessmt2zelem z145 y151) P.&&
    (tip2015sortSSortPermutessmt2zisPermutation
       xs95 (tip2015sortSSortPermutessmt2zdelete z145 y151))
tip2015sortStoogeSortIsSortsmt2ztake ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a67 ->
      Grammarssimpexprunambig3smt2list a67
tip2015sortStoogeSortIsSortsmt2ztake x155 y152 =
  case x155 P.== (0) of
    P.True -> Nil :: Grammarssimpexprunambig3smt2list a67
    P.False ->
      case y152 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a67
        Cons z146 xs96 ->
          Cons
            z146 (tip2015sortStoogeSortIsSortsmt2ztake (x155 P.- (1)) xs96)
tip2015sortStoogeSortIsSortsmt2zlength ::
  Grammarssimpexprunambig3smt2list a68 -> P.Int
tip2015sortStoogeSortIsSortsmt2zlength Nil = 0
tip2015sortStoogeSortIsSortsmt2zlength (Cons y153 xs97) =
  (1) P.+ (tip2015sortStoogeSortIsSortsmt2zlength xs97)
tip2015sortStoogeSortIsSortsmt2zdrop ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a69 ->
      Grammarssimpexprunambig3smt2list a69
tip2015sortStoogeSortIsSortsmt2zdrop x156 y154 =
  case x156 P.== (0) of
    P.True -> y154
    P.False ->
      case y154 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a69
        Cons z147 xs114 ->
          tip2015sortStoogeSortIsSortsmt2zdrop (x156 P.- (1)) xs114
tip2015sortStoogeSortIsSortsmt2zsplitAt ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a70 ->
      Isaplannerprop45smt2Pair
        (Grammarssimpexprunambig3smt2list a70)
        (Grammarssimpexprunambig3smt2list a70)
tip2015sortStoogeSortIsSortsmt2zsplitAt x157 y155 =
  Pair2
    (tip2015sortStoogeSortIsSortsmt2ztake x157 y155)
    (tip2015sortStoogeSortIsSortsmt2zdrop x157 y155)
tip2015sortStoogeSortIsSortsmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortIsSortsmt2sort2 x158 y156 =
  case x158 P.<= y156 of
    P.True ->
      Cons
        x158 (Cons y156 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y156 (Cons x158 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortStoogeSortIsSortsmt2insert2 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortIsSortsmt2insert2 x159 Nil =
  Cons x159 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortStoogeSortIsSortsmt2insert2 x159 (Cons z148 xs98) =
  case x159 P.<= z148 of
    P.True -> Cons x159 (Cons z148 xs98)
    P.False ->
      Cons z148 (tip2015sortStoogeSortIsSortsmt2insert2 x159 xs98)
tip2015sortStoogeSortIsSortsmt2isort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortIsSortsmt2isort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortIsSortsmt2isort (Cons y157 xs99) =
  tip2015sortStoogeSortIsSortsmt2insert2
    y157 (tip2015sortStoogeSortIsSortsmt2isort xs99)
tip2015sortStoogeSortIsSortsmt2stooge1sort2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortIsSortsmt2stooge1sort2 x160 =
  case tip2015sortStoogeSortIsSortsmt2zsplitAt
         (P.div (tip2015sortStoogeSortIsSortsmt2zlength x160) (3))
         (isaplannerprop85smt2rev x160) of
    Pair2 ys66 zs13 ->
      append
        (tip2015sortStoogeSortIsSortsmt2stoogesort zs13)
        (isaplannerprop85smt2rev ys66)
tip2015sortStoogeSortIsSortsmt2stoogesort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortIsSortsmt2stoogesort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortIsSortsmt2stoogesort (Cons y158 Nil) =
  Cons y158 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortStoogeSortIsSortsmt2stoogesort
  (Cons y158 (Cons y233 Nil)) =
  tip2015sortStoogeSortIsSortsmt2sort2 y158 y233
tip2015sortStoogeSortIsSortsmt2stoogesort
  (Cons y158 (Cons y233 (Cons x338 x431))) =
  tip2015sortStoogeSortIsSortsmt2stooge1sort2
    (tip2015sortStoogeSortIsSortsmt2stooge1sort1
       (tip2015sortStoogeSortIsSortsmt2stooge1sort2
          (Cons y158 (Cons y233 (Cons x338 x431)))))
tip2015sortStoogeSortIsSortsmt2stooge1sort1 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortIsSortsmt2stooge1sort1 x161 =
  case tip2015sortStoogeSortIsSortsmt2zsplitAt
         (P.div (tip2015sortStoogeSortIsSortsmt2zlength x161) (3)) x161 of
    Pair2 ys67 zs14 ->
      append ys67 (tip2015sortStoogeSortIsSortsmt2stoogesort zs14)
flatten1 ::
  Grammarssimpexprunambig3smt2list
    (Tip2015treesortAddSamesmt2Tree a71) ->
    Grammarssimpexprunambig3smt2list a71
flatten1 Nil = Nil :: Grammarssimpexprunambig3smt2list a71
flatten1
  (Cons
     (Tip2015treesortAddSamesmt2Node
        (Tip2015treesortAddSamesmt2Node x339 x432 x513) x260 q11)
     ps) =
  flatten1
    (Cons
       (Tip2015treesortAddSamesmt2Node x339 x432 x513)
       (Cons
          (Tip2015treesortAddSamesmt2Node
             (Tip2015treesortAddSamesmt2Nil ::
                Tip2015treesortAddSamesmt2Tree a71)
             x260 q11)
          ps))
flatten1
  (Cons
     (Tip2015treesortAddSamesmt2Node
        Tip2015treesortAddSamesmt2Nil x260 q11)
     ps) =
  Cons x260 (flatten1 (Cons q11 ps))
flatten1 (Cons Tip2015treesortAddSamesmt2Nil ps) = flatten1 ps
concatMap ::
  (a72 -> Grammarssimpexprunambig3smt2list b15) ->
    Grammarssimpexprunambig3smt2list a72 ->
      Grammarssimpexprunambig3smt2list b15
concatMap x162 Nil = Nil :: Grammarssimpexprunambig3smt2list b15
concatMap x162 (Cons z149 xs100) =
  append (P.id x162 z149) (concatMap x162 xs100)
tip2015sortQSortCountsmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015sortQSortCountsmt2zcount x163 Nil = Isaplannerprop54smt2Z
tip2015sortQSortCountsmt2zcount x163 (Cons z150 xs101) =
  case x163 P.== z150 of
    P.True ->
      Isaplannerprop54smt2S (tip2015sortQSortCountsmt2zcount x163 xs101)
    P.False -> tip2015sortQSortCountsmt2zcount x163 xs101
tip2015sortStoogeSortSortssmt2ztake ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a73 ->
      Grammarssimpexprunambig3smt2list a73
tip2015sortStoogeSortSortssmt2ztake x164 y159 =
  case x164 P.== (0) of
    P.True -> Nil :: Grammarssimpexprunambig3smt2list a73
    P.False ->
      case y159 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a73
        Cons z151 xs102 ->
          Cons
            z151 (tip2015sortStoogeSortSortssmt2ztake (x164 P.- (1)) xs102)
tip2015sortStoogeSortSortssmt2zisaplannerprop78smt2sorted ::
  Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortStoogeSortSortssmt2zisaplannerprop78smt2sorted Nil =
  P.True
tip2015sortStoogeSortSortssmt2zisaplannerprop78smt2sorted
  (Cons y160 Nil) =
  P.True
tip2015sortStoogeSortSortssmt2zisaplannerprop78smt2sorted
  (Cons y160 (Cons y234 xs103)) =
  (y160 P.<= y234) P.&&
    (tip2015sortStoogeSortSortssmt2zisaplannerprop78smt2sorted
       (Cons y234 xs103))
tip2015sortStoogeSortSortssmt2zlength ::
  Grammarssimpexprunambig3smt2list a74 -> P.Int
tip2015sortStoogeSortSortssmt2zlength Nil = 0
tip2015sortStoogeSortSortssmt2zlength (Cons y161 xs104) =
  (1) P.+ (tip2015sortStoogeSortSortssmt2zlength xs104)
tip2015sortStoogeSortSortssmt2zdrop ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a75 ->
      Grammarssimpexprunambig3smt2list a75
tip2015sortStoogeSortSortssmt2zdrop x165 y162 =
  case x165 P.== (0) of
    P.True -> y162
    P.False ->
      case y162 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a75
        Cons z152 xs115 ->
          tip2015sortStoogeSortSortssmt2zdrop (x165 P.- (1)) xs115
tip2015sortStoogeSortSortssmt2zsplitAt ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a76 ->
      Isaplannerprop45smt2Pair
        (Grammarssimpexprunambig3smt2list a76)
        (Grammarssimpexprunambig3smt2list a76)
tip2015sortStoogeSortSortssmt2zsplitAt x166 y163 =
  Pair2
    (tip2015sortStoogeSortSortssmt2ztake x166 y163)
    (tip2015sortStoogeSortSortssmt2zdrop x166 y163)
tip2015sortStoogeSortSortssmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortSortssmt2sort2 x167 y164 =
  case x167 P.<= y164 of
    P.True ->
      Cons
        x167 (Cons y164 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y164 (Cons x167 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortStoogeSortSortssmt2stooge1sort2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortSortssmt2stooge1sort2 x168 =
  case tip2015sortStoogeSortSortssmt2zsplitAt
         (P.div (tip2015sortStoogeSortSortssmt2zlength x168) (3))
         (isaplannerprop85smt2rev x168) of
    Pair2 ys68 zs15 ->
      append
        (tip2015sortStoogeSortSortssmt2stoogesort zs15)
        (isaplannerprop85smt2rev ys68)
tip2015sortStoogeSortSortssmt2stoogesort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortSortssmt2stoogesort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortSortssmt2stoogesort (Cons y165 Nil) =
  Cons y165 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortStoogeSortSortssmt2stoogesort
  (Cons y165 (Cons y235 Nil)) =
  tip2015sortStoogeSortSortssmt2sort2 y165 y235
tip2015sortStoogeSortSortssmt2stoogesort
  (Cons y165 (Cons y235 (Cons x340 x433))) =
  tip2015sortStoogeSortSortssmt2stooge1sort2
    (tip2015sortStoogeSortSortssmt2stooge1sort1
       (tip2015sortStoogeSortSortssmt2stooge1sort2
          (Cons y165 (Cons y235 (Cons x340 x433)))))
tip2015sortStoogeSortSortssmt2stooge1sort1 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortSortssmt2stooge1sort1 x169 =
  case tip2015sortStoogeSortSortssmt2zsplitAt
         (P.div (tip2015sortStoogeSortSortssmt2zlength x169) (3)) x169 of
    Pair2 ys69 zs16 ->
      append ys69 (tip2015sortStoogeSortSortssmt2stoogesort zs16)
mul2 ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
mul2 Isaplannerprop54smt2Z y166 = Isaplannerprop54smt2Z
mul2 (Isaplannerprop54smt2S z153) Isaplannerprop54smt2Z =
  Isaplannerprop54smt2Z
mul2 (Isaplannerprop54smt2S z153) (Isaplannerprop54smt2S x261) =
  Isaplannerprop54smt2S (add3acc z153 x261 (mul2 z153 x261))
tip2015sortHSortSortssmt2zisaplannerprop78smt2sorted ::
  Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortHSortSortssmt2zisaplannerprop78smt2sorted Nil = P.True
tip2015sortHSortSortssmt2zisaplannerprop78smt2sorted
  (Cons y167 Nil) =
  P.True
tip2015sortHSortSortssmt2zisaplannerprop78smt2sorted
  (Cons y167 (Cons y236 xs105)) =
  (y167 P.<= y236) P.&&
    (tip2015sortHSortSortssmt2zisaplannerprop78smt2sorted
       (Cons y236 xs105))
tip2015sortHSortSortssmt2toHeap2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list
      (Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortHSortSortssmt2toHeap2 Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortHSortSortssmt2toHeap2 (Cons y168 z154) =
  Cons
    (Tip2015treesortAddSamesmt2Node
       (Tip2015treesortAddSamesmt2Nil ::
          Tip2015treesortAddSamesmt2Tree P.Int)
       y168
       (Tip2015treesortAddSamesmt2Nil ::
          Tip2015treesortAddSamesmt2Tree P.Int))
    (tip2015sortHSortSortssmt2toHeap2 z154)
tip2015sortHSortSortssmt2hmerge ::
  Tip2015treesortAddSamesmt2Tree P.Int ->
    Tip2015treesortAddSamesmt2Tree P.Int ->
      Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortHSortSortssmt2hmerge
  (Tip2015treesortAddSamesmt2Node z155 x262 x341)
  (Tip2015treesortAddSamesmt2Node x434 x514 x613) =
  case x262 P.<= x514 of
    P.True ->
      Tip2015treesortAddSamesmt2Node
        (tip2015sortHSortSortssmt2hmerge
           x341 (Tip2015treesortAddSamesmt2Node x434 x514 x613))
        x262 z155
    P.False ->
      Tip2015treesortAddSamesmt2Node
        (tip2015sortHSortSortssmt2hmerge
           (Tip2015treesortAddSamesmt2Node z155 x262 x341) x613)
        x514 x434
tip2015sortHSortSortssmt2hmerge
  (Tip2015treesortAddSamesmt2Node z155 x262 x341)
  Tip2015treesortAddSamesmt2Nil =
  Tip2015treesortAddSamesmt2Node z155 x262 x341
tip2015sortHSortSortssmt2hmerge
  Tip2015treesortAddSamesmt2Nil y169 =
  y169
tip2015sortHSortSortssmt2hpairwise ::
  Grammarssimpexprunambig3smt2list
    (Tip2015treesortAddSamesmt2Tree P.Int) ->
    Grammarssimpexprunambig3smt2list
      (Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortHSortSortssmt2hpairwise Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortHSortSortssmt2hpairwise (Cons p9 Nil) =
  Cons
    p9
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Tip2015treesortAddSamesmt2Tree P.Int))
tip2015sortHSortSortssmt2hpairwise (Cons p9 (Cons q12 qs)) =
  Cons
    (tip2015sortHSortSortssmt2hmerge p9 q12)
    (tip2015sortHSortSortssmt2hpairwise qs)
tip2015sortHSortSortssmt2hmerging ::
  Grammarssimpexprunambig3smt2list
    (Tip2015treesortAddSamesmt2Tree P.Int) ->
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortHSortSortssmt2hmerging Nil =
  Tip2015treesortAddSamesmt2Nil ::
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortHSortSortssmt2hmerging (Cons p10 Nil) = p10
tip2015sortHSortSortssmt2hmerging (Cons p10 (Cons z156 x263)) =
  tip2015sortHSortSortssmt2hmerging
    (tip2015sortHSortSortssmt2hpairwise (Cons p10 (Cons z156 x263)))
tip2015sortHSortSortssmt2toHeap ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortHSortSortssmt2toHeap x170 =
  tip2015sortHSortSortssmt2hmerging
    (tip2015sortHSortSortssmt2toHeap2 x170)
tip2015sortHSortSortssmt2toList ::
  Tip2015treesortAddSamesmt2Tree P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortHSortSortssmt2toList
  (Tip2015treesortAddSamesmt2Node p11 y170 q13) =
  Cons
    y170
    (tip2015sortHSortSortssmt2toList
       (tip2015sortHSortSortssmt2hmerge p11 q13))
tip2015sortHSortSortssmt2toList Tip2015treesortAddSamesmt2Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortHSortSortssmt2hsort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortHSortSortssmt2hsort x171 =
  tip2015sortHSortSortssmt2toList
    (tip2015sortHSortSortssmt2toHeap x171)
tip2015sortNMSortTDPermutessmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortNMSortTDPermutessmt2zelem x172 Nil = P.False
tip2015sortNMSortTDPermutessmt2zelem x172 (Cons z157 ys70) =
  (x172 P.== z157) P.||
    (tip2015sortNMSortTDPermutessmt2zelem x172 ys70)
tip2015sortNMSortTDPermutessmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortNMSortTDPermutessmt2zdelete x173 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNMSortTDPermutessmt2zdelete x173 (Cons z158 ys71) =
  case x173 P.== z158 of
    P.True -> ys71
    P.False ->
      Cons z158 (tip2015sortNMSortTDPermutessmt2zdelete x173 ys71)
tip2015sortNMSortTDPermutessmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortNMSortTDPermutessmt2zisPermutation Nil y171 = null y171
tip2015sortNMSortTDPermutessmt2zisPermutation
  (Cons z159 xs106) y171 =
  (tip2015sortNMSortTDPermutessmt2zelem z159 y171) P.&&
    (tip2015sortNMSortTDPermutessmt2zisPermutation
       xs106 (tip2015sortNMSortTDPermutessmt2zdelete z159 y171))
tip2015sortNMSortTDPermutessmt2lmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortNMSortTDPermutessmt2lmerge Nil y172 = y172
tip2015sortNMSortTDPermutessmt2lmerge (Cons z160 x264) Nil =
  Cons z160 x264
tip2015sortNMSortTDPermutessmt2lmerge
  (Cons z160 x264) (Cons x342 x435) =
  case z160 P.<= x342 of
    P.True ->
      Cons
        z160 (tip2015sortNMSortTDPermutessmt2lmerge x264 (Cons x342 x435))
    P.False ->
      Cons
        x342 (tip2015sortNMSortTDPermutessmt2lmerge (Cons z160 x264) x435)
tip2015sortNMSortTDPermutessmt2nmsorttd ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNMSortTDPermutessmt2nmsorttd Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNMSortTDPermutessmt2nmsorttd (Cons y173 Nil) =
  Cons y173 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortNMSortTDPermutessmt2nmsorttd
  (Cons y173 (Cons x265 x343)) =
  let k4 =
        half (isaplannerprop68smt2len (Cons y173 (Cons x265 x343)))
    in tip2015sortNMSortTDPermutessmt2lmerge
         (tip2015sortNMSortTDPermutessmt2nmsorttd
            (isaplannerprop82smt2take k4 (Cons y173 (Cons x265 x343))))
         (tip2015sortNMSortTDPermutessmt2nmsorttd
            (isaplannerprop12smt2drop k4 (Cons y173 (Cons x265 x343))))
mod2 ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
mod2 x174 Isaplannerprop54smt2Z = Isaplannerprop54smt2Z
mod2 x174 (Isaplannerprop54smt2S z161) =
  case isaplannerprop65smt2lt x174 (Isaplannerprop54smt2S z161) of
    P.True -> x174
    P.False ->
      mod2
        (isaplannerprop54smt2minus x174 (Isaplannerprop54smt2S z161))
        (Isaplannerprop54smt2S z161)
tip2015sortSSortIsSortsmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortIsSortsmt2zdelete x175 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortIsSortsmt2zdelete x175 (Cons z162 ys72) =
  case x175 P.== z162 of
    P.True -> ys72
    P.False -> Cons z162 (tip2015sortSSortIsSortsmt2zdelete x175 ys72)
tip2015sortSSortIsSortsmt2ssortminimum ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Int
tip2015sortSSortIsSortsmt2ssortminimum x176 Nil = x176
tip2015sortSSortIsSortsmt2ssortminimum x176 (Cons z163 ys73) =
  case z163 P.<= x176 of
    P.True -> tip2015sortSSortIsSortsmt2ssortminimum z163 ys73
    P.False -> tip2015sortSSortIsSortsmt2ssortminimum x176 ys73
tip2015sortSSortIsSortsmt2ssort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortIsSortsmt2ssort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortIsSortsmt2ssort (Cons y174 ys74) =
  let m10 = tip2015sortSSortIsSortsmt2ssortminimum y174 ys74
    in Cons
         m10
         (tip2015sortSSortIsSortsmt2ssort
            (tip2015sortSSortIsSortsmt2zdelete m10 (Cons y174 ys74)))
tip2015sortSSortIsSortsmt2insert2 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortIsSortsmt2insert2 x177 Nil =
  Cons x177 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortSSortIsSortsmt2insert2 x177 (Cons z164 xs107) =
  case x177 P.<= z164 of
    P.True -> Cons x177 (Cons z164 xs107)
    P.False -> Cons z164 (tip2015sortSSortIsSortsmt2insert2 x177 xs107)
tip2015sortSSortIsSortsmt2isort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortIsSortsmt2isort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortIsSortsmt2isort (Cons y175 xs108) =
  tip2015sortSSortIsSortsmt2insert2
    y175 (tip2015sortSSortIsSortsmt2isort xs108)
tip2015sortStoogeSort2Sortssmt2ztake ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a77 ->
      Grammarssimpexprunambig3smt2list a77
tip2015sortStoogeSort2Sortssmt2ztake x178 y176 =
  case x178 P.== (0) of
    P.True -> Nil :: Grammarssimpexprunambig3smt2list a77
    P.False ->
      case y176 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a77
        Cons z165 xs109 ->
          Cons
            z165 (tip2015sortStoogeSort2Sortssmt2ztake (x178 P.- (1)) xs109)
tip2015sortStoogeSort2Sortssmt2zisaplannerprop78smt2sorted ::
  Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortStoogeSort2Sortssmt2zisaplannerprop78smt2sorted Nil =
  P.True
tip2015sortStoogeSort2Sortssmt2zisaplannerprop78smt2sorted
  (Cons y177 Nil) =
  P.True
tip2015sortStoogeSort2Sortssmt2zisaplannerprop78smt2sorted
  (Cons y177 (Cons y237 xs116)) =
  (y177 P.<= y237) P.&&
    (tip2015sortStoogeSort2Sortssmt2zisaplannerprop78smt2sorted
       (Cons y237 xs116))
tip2015sortStoogeSort2Sortssmt2zlength ::
  Grammarssimpexprunambig3smt2list a78 -> P.Int
tip2015sortStoogeSort2Sortssmt2zlength Nil = 0
tip2015sortStoogeSort2Sortssmt2zlength (Cons y178 xs117) =
  (1) P.+ (tip2015sortStoogeSort2Sortssmt2zlength xs117)
tip2015sortStoogeSort2Sortssmt2zdrop ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a79 ->
      Grammarssimpexprunambig3smt2list a79
tip2015sortStoogeSort2Sortssmt2zdrop x179 y179 =
  case x179 P.== (0) of
    P.True -> y179
    P.False ->
      case y179 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a79
        Cons z166 xs118 ->
          tip2015sortStoogeSort2Sortssmt2zdrop (x179 P.- (1)) xs118
tip2015sortStoogeSort2Sortssmt2zsplitAt ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a80 ->
      Isaplannerprop45smt2Pair
        (Grammarssimpexprunambig3smt2list a80)
        (Grammarssimpexprunambig3smt2list a80)
tip2015sortStoogeSort2Sortssmt2zsplitAt x180 y180 =
  Pair2
    (tip2015sortStoogeSort2Sortssmt2ztake x180 y180)
    (tip2015sortStoogeSort2Sortssmt2zdrop x180 y180)
tip2015sortStoogeSort2Sortssmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSort2Sortssmt2sort2 x181 y181 =
  case x181 P.<= y181 of
    P.True ->
      Cons
        x181 (Cons y181 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y181 (Cons x181 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortMSortBU2IsSortsmt2risers ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBU2IsSortsmt2risers Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBU2IsSortsmt2risers (Cons y182 Nil) =
  Cons
    (Cons y182 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Grammarssimpexprunambig3smt2list P.Int))
tip2015sortMSortBU2IsSortsmt2risers (Cons y182 (Cons y238 xs119)) =
  case y182 P.<= y238 of
    P.True ->
      case tip2015sortMSortBU2IsSortsmt2risers (Cons y238 xs119) of
        Nil ->
          Nil ::
            Grammarssimpexprunambig3smt2list
              (Grammarssimpexprunambig3smt2list P.Int)
        Cons ys75 yss3 -> Cons (Cons y182 ys75) yss3
    P.False ->
      Cons
        (Cons y182 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
        (tip2015sortMSortBU2IsSortsmt2risers (Cons y238 xs119))
tip2015sortMSortBU2IsSortsmt2lmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2IsSortsmt2lmerge Nil y183 = y183
tip2015sortMSortBU2IsSortsmt2lmerge (Cons z167 x266) Nil =
  Cons z167 x266
tip2015sortMSortBU2IsSortsmt2lmerge
  (Cons z167 x266) (Cons x344 x436) =
  case z167 P.<= x344 of
    P.True ->
      Cons
        z167 (tip2015sortMSortBU2IsSortsmt2lmerge x266 (Cons x344 x436))
    P.False ->
      Cons
        x344 (tip2015sortMSortBU2IsSortsmt2lmerge (Cons z167 x266) x436)
tip2015sortMSortBU2IsSortsmt2pairwise ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list P.Int) ->
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBU2IsSortsmt2pairwise Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBU2IsSortsmt2pairwise (Cons xs120 Nil) =
  Cons
    xs120
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Grammarssimpexprunambig3smt2list P.Int))
tip2015sortMSortBU2IsSortsmt2pairwise
  (Cons xs120 (Cons ys76 xss8)) =
  Cons
    (tip2015sortMSortBU2IsSortsmt2lmerge xs120 ys76)
    (tip2015sortMSortBU2IsSortsmt2pairwise xss8)
tip2015sortMSortBU2IsSortsmt2mergingbu2 ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list P.Int) ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2IsSortsmt2mergingbu2 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2IsSortsmt2mergingbu2 (Cons xs121 Nil) = xs121
tip2015sortMSortBU2IsSortsmt2mergingbu2
  (Cons xs121 (Cons z168 x267)) =
  tip2015sortMSortBU2IsSortsmt2mergingbu2
    (tip2015sortMSortBU2IsSortsmt2pairwise
       (Cons xs121 (Cons z168 x267)))
tip2015sortMSortBU2IsSortsmt2msortbu2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2IsSortsmt2msortbu2 x182 =
  tip2015sortMSortBU2IsSortsmt2mergingbu2
    (tip2015sortMSortBU2IsSortsmt2risers x182)
tip2015sortMSortBU2IsSortsmt2insert2 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2IsSortsmt2insert2 x183 Nil =
  Cons x183 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBU2IsSortsmt2insert2 x183 (Cons z169 xs122) =
  case x183 P.<= z169 of
    P.True -> Cons x183 (Cons z169 xs122)
    P.False ->
      Cons z169 (tip2015sortMSortBU2IsSortsmt2insert2 x183 xs122)
tip2015sortMSortBU2IsSortsmt2isort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2IsSortsmt2isort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2IsSortsmt2isort (Cons y184 xs123) =
  tip2015sortMSortBU2IsSortsmt2insert2
    y184 (tip2015sortMSortBU2IsSortsmt2isort xs123)
tip2015substSubstFreeYessmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015substSubstFreeYessmt2zelem x184 Nil = P.False
tip2015substSubstFreeYessmt2zelem x184 (Cons z170 ys77) =
  (x184 P.== z170) P.|| (tip2015substSubstFreeYessmt2zelem x184 ys77)
tip2015substSubstFreeYessmt2newmaximum ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Int
tip2015substSubstFreeYessmt2newmaximum x185 Nil = x185
tip2015substSubstFreeYessmt2newmaximum x185 (Cons z171 ys78) =
  case x185 P.<= z171 of
    P.True -> tip2015substSubstFreeYessmt2newmaximum z171 ys78
    P.False -> tip2015substSubstFreeYessmt2newmaximum x185 ys78
tip2015substSubstFreeYessmt2new ::
  Grammarssimpexprunambig3smt2list P.Int -> P.Int
tip2015substSubstFreeYessmt2new x186 =
  (tip2015substSubstFreeYessmt2newmaximum (0) x186) P.+ (1)
tip2015substSubstFreeYessmt2free ::
  Tip2015substSubstFreeYessmt2Expr ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015substSubstFreeYessmt2free
  (Tip2015substSubstFreeYessmt2Var y185) =
  Cons y185 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015substSubstFreeYessmt2free
  (Tip2015substSubstFreeYessmt2Lam z172 b16) =
  filter
    (\ x268 -> z172 P./= x268) (tip2015substSubstFreeYessmt2free b16)
tip2015substSubstFreeYessmt2free
  (Tip2015substSubstFreeYessmt2App a211 b25) =
  append
    (tip2015substSubstFreeYessmt2free a211)
    (tip2015substSubstFreeYessmt2free b25)
tip2015substSubstFreeYessmt2subst ::
  P.Int ->
    Tip2015substSubstFreeYessmt2Expr ->
      Tip2015substSubstFreeYessmt2Expr ->
        Tip2015substSubstFreeYessmt2Expr
tip2015substSubstFreeYessmt2subst
  x187 y186 (Tip2015substSubstFreeYessmt2Var y239) =
  case x187 P.== y239 of
    P.True -> y186
    P.False -> Tip2015substSubstFreeYessmt2Var y239
tip2015substSubstFreeYessmt2subst
  x187 y186 (Tip2015substSubstFreeYessmt2Lam y310 a81) =
  let z210 =
        tip2015substSubstFreeYessmt2new
          (append
             (tip2015substSubstFreeYessmt2free y186)
             (tip2015substSubstFreeYessmt2free a81))
    in case x187 P.== y310 of
         P.True -> Tip2015substSubstFreeYessmt2Lam y310 a81
         P.False ->
           case tip2015substSubstFreeYessmt2zelem
                  y310 (tip2015substSubstFreeYessmt2free y186) of
             P.True ->
               tip2015substSubstFreeYessmt2subst
                 x187 y186
                 (Tip2015substSubstFreeYessmt2Lam
                    z210
                    (tip2015substSubstFreeYessmt2subst
                       y310 (Tip2015substSubstFreeYessmt2Var z210) a81))
             P.False ->
               Tip2015substSubstFreeYessmt2Lam
                 y310 (tip2015substSubstFreeYessmt2subst x187 y186 a81)
tip2015substSubstFreeYessmt2subst
  x187 y186 (Tip2015substSubstFreeYessmt2App c9 b26) =
  Tip2015substSubstFreeYessmt2App
    (tip2015substSubstFreeYessmt2subst x187 y186 c9)
    (tip2015substSubstFreeYessmt2subst x187 y186 b26)
tip2015sortQSortSortssmt2zisaplannerprop78smt2sorted ::
  Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortQSortSortssmt2zisaplannerprop78smt2sorted Nil = P.True
tip2015sortQSortSortssmt2zisaplannerprop78smt2sorted
  (Cons y187 Nil) =
  P.True
tip2015sortQSortSortssmt2zisaplannerprop78smt2sorted
  (Cons y187 (Cons y240 xs124)) =
  (y187 P.<= y240) P.&&
    (tip2015sortQSortSortssmt2zisaplannerprop78smt2sorted
       (Cons y240 xs124))
tip2015sortNStoogeSortSortssmt2zisaplannerprop78smt2sorted ::
  Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortNStoogeSortSortssmt2zisaplannerprop78smt2sorted Nil =
  P.True
tip2015sortNStoogeSortSortssmt2zisaplannerprop78smt2sorted
  (Cons y188 Nil) =
  P.True
tip2015sortNStoogeSortSortssmt2zisaplannerprop78smt2sorted
  (Cons y188 (Cons y241 xs125)) =
  (y188 P.<= y241) P.&&
    (tip2015sortNStoogeSortSortssmt2zisaplannerprop78smt2sorted
       (Cons y241 xs125))
tip2015sortNStoogeSortSortssmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortSortssmt2sort2 x188 y189 =
  case x188 P.<= y189 of
    P.True ->
      Cons
        x188 (Cons y189 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y189 (Cons x188 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortNStoogeSortSortssmt2nstooge1sort2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortSortssmt2nstooge1sort2 x189 =
  case tip2015sortNStoogeSort2Countsmt2splitAt
         (third (isaplannerprop68smt2len x189))
         (isaplannerprop85smt2rev x189) of
    Pair2 ys79 zs17 ->
      append
        (tip2015sortNStoogeSortSortssmt2nstoogesort zs17)
        (isaplannerprop85smt2rev ys79)
tip2015sortNStoogeSortSortssmt2nstoogesort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortSortssmt2nstoogesort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortSortssmt2nstoogesort (Cons y190 Nil) =
  Cons y190 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortNStoogeSortSortssmt2nstoogesort
  (Cons y190 (Cons y242 Nil)) =
  tip2015sortNStoogeSortSortssmt2sort2 y190 y242
tip2015sortNStoogeSortSortssmt2nstoogesort
  (Cons y190 (Cons y242 (Cons x345 x437))) =
  tip2015sortNStoogeSortSortssmt2nstooge1sort2
    (tip2015sortNStoogeSortSortssmt2nstooge1sort1
       (tip2015sortNStoogeSortSortssmt2nstooge1sort2
          (Cons y190 (Cons y242 (Cons x345 x437)))))
tip2015sortNStoogeSortSortssmt2nstooge1sort1 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortSortssmt2nstooge1sort1 x190 =
  case tip2015sortNStoogeSort2Countsmt2splitAt
         (third (isaplannerprop68smt2len x190)) x190 of
    Pair2 ys80 zs18 ->
      append ys80 (tip2015sortNStoogeSortSortssmt2nstoogesort zs18)
tip2015sortISortSortssmt2zisaplannerprop78smt2sorted ::
  Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortISortSortssmt2zisaplannerprop78smt2sorted Nil = P.True
tip2015sortISortSortssmt2zisaplannerprop78smt2sorted
  (Cons y191 Nil) =
  P.True
tip2015sortISortSortssmt2zisaplannerprop78smt2sorted
  (Cons y191 (Cons y243 xs126)) =
  (y191 P.<= y243) P.&&
    (tip2015sortISortSortssmt2zisaplannerprop78smt2sorted
       (Cons y243 xs126))
tip2015sortISortSortssmt2insert2 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortISortSortssmt2insert2 x191 Nil =
  Cons x191 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortISortSortssmt2insert2 x191 (Cons z173 xs127) =
  case x191 P.<= z173 of
    P.True -> Cons x191 (Cons z173 xs127)
    P.False -> Cons z173 (tip2015sortISortSortssmt2insert2 x191 xs127)
tip2015sortISortSortssmt2isort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortISortSortssmt2isort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortISortSortssmt2isort (Cons y192 xs128) =
  tip2015sortISortSortssmt2insert2
    y192 (tip2015sortISortSortssmt2isort xs128)
tip2015sortBSortIsSortsmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortIsSortsmt2sort2 x192 y193 =
  case x192 P.<= y193 of
    P.True ->
      Cons
        x192 (Cons y193 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y193 (Cons x192 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortBSortIsSortsmt2insert2 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortIsSortsmt2insert2 x193 Nil =
  Cons x193 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortBSortIsSortsmt2insert2 x193 (Cons z174 xs129) =
  case x193 P.<= z174 of
    P.True -> Cons x193 (Cons z174 xs129)
    P.False -> Cons z174 (tip2015sortBSortIsSortsmt2insert2 x193 xs129)
tip2015sortBSortIsSortsmt2isort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortIsSortsmt2isort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortIsSortsmt2isort (Cons y194 xs130) =
  tip2015sortBSortIsSortsmt2insert2
    y194 (tip2015sortBSortIsSortsmt2isort xs130)
tip2015sortBSortIsSortsmt2evens ::
  Grammarssimpexprunambig3smt2list a82 ->
    Grammarssimpexprunambig3smt2list a82
tip2015sortBSortIsSortsmt2evens Nil =
  Nil :: Grammarssimpexprunambig3smt2list a82
tip2015sortBSortIsSortsmt2evens (Cons y195 xs131) =
  Cons y195 (tip2015sortBSortIsSortsmt2odds xs131)
tip2015sortBSortIsSortsmt2odds ::
  Grammarssimpexprunambig3smt2list a83 ->
    Grammarssimpexprunambig3smt2list a83
tip2015sortBSortIsSortsmt2odds Nil =
  Nil :: Grammarssimpexprunambig3smt2list a83
tip2015sortBSortIsSortsmt2odds (Cons y196 xs132) =
  tip2015sortBSortIsSortsmt2evens xs132
tip2015sortBSortIsSortsmt2pairs ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortIsSortsmt2pairs Nil y197 = y197
tip2015sortBSortIsSortsmt2pairs (Cons z175 x269) Nil =
  Cons z175 x269
tip2015sortBSortIsSortsmt2pairs (Cons z175 x269) (Cons x346 x438) =
  append
    (tip2015sortBSortIsSortsmt2sort2 z175 x346)
    (tip2015sortBSortIsSortsmt2pairs x269 x438)
tip2015sortBSortIsSortsmt2stitch ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortIsSortsmt2stitch Nil y198 = y198
tip2015sortBSortIsSortsmt2stitch (Cons z176 xs133) y198 =
  Cons z176 (tip2015sortBSortIsSortsmt2pairs xs133 y198)
tip2015sortBSortIsSortsmt2bmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortIsSortsmt2bmerge Nil y199 =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortIsSortsmt2bmerge (Cons z177 x270) Nil =
  Cons z177 x270
tip2015sortBSortIsSortsmt2bmerge (Cons z177 Nil) (Cons x347 Nil) =
  tip2015sortBSortIsSortsmt2sort2 z177 x347
tip2015sortBSortIsSortsmt2bmerge
  (Cons z177 Nil) (Cons x347 (Cons x515 x614)) =
  tip2015sortBSortIsSortsmt2stitch
    (tip2015sortBSortIsSortsmt2bmerge
       (tip2015sortBSortIsSortsmt2evens
          (Cons z177 (Nil :: Grammarssimpexprunambig3smt2list P.Int)))
       (tip2015sortBSortIsSortsmt2evens (Cons x347 (Cons x515 x614))))
    (tip2015sortBSortIsSortsmt2bmerge
       (tip2015sortBSortIsSortsmt2odds
          (Cons z177 (Nil :: Grammarssimpexprunambig3smt2list P.Int)))
       (tip2015sortBSortIsSortsmt2odds (Cons x347 (Cons x515 x614))))
tip2015sortBSortIsSortsmt2bmerge
  (Cons z177 (Cons x711 x811)) (Cons x347 x439) =
  tip2015sortBSortIsSortsmt2stitch
    (tip2015sortBSortIsSortsmt2bmerge
       (tip2015sortBSortIsSortsmt2evens (Cons z177 (Cons x711 x811)))
       (tip2015sortBSortIsSortsmt2evens (Cons x347 x439)))
    (tip2015sortBSortIsSortsmt2bmerge
       (tip2015sortBSortIsSortsmt2odds (Cons z177 (Cons x711 x811)))
       (tip2015sortBSortIsSortsmt2odds (Cons x347 x439)))
tip2015sortBSortIsSortsmt2bsort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortIsSortsmt2bsort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortIsSortsmt2bsort (Cons y200 Nil) =
  Cons y200 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortBSortIsSortsmt2bsort (Cons y200 (Cons x271 x348)) =
  tip2015sortBSortIsSortsmt2bmerge
    (tip2015sortBSortIsSortsmt2bsort
       (tip2015sortBSortIsSortsmt2evens (Cons y200 (Cons x271 x348))))
    (tip2015sortBSortIsSortsmt2bsort
       (tip2015sortBSortIsSortsmt2odds (Cons y200 (Cons x271 x348))))
tip2015sortBubSortIsSortsmt2insert2 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortBubSortIsSortsmt2insert2 x194 Nil =
  Cons x194 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortBubSortIsSortsmt2insert2 x194 (Cons z178 xs134) =
  case x194 P.<= z178 of
    P.True -> Cons x194 (Cons z178 xs134)
    P.False ->
      Cons z178 (tip2015sortBubSortIsSortsmt2insert2 x194 xs134)
tip2015sortBubSortIsSortsmt2isort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortBubSortIsSortsmt2isort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortBubSortIsSortsmt2isort (Cons y201 xs135) =
  tip2015sortBubSortIsSortsmt2insert2
    y201 (tip2015sortBubSortIsSortsmt2isort xs135)
tip2015sortBubSortIsSortsmt2bubble ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Isaplannerprop45smt2Pair
      P.Bool (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortBubSortIsSortsmt2bubble Nil =
  Pair2 P.False (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortBubSortIsSortsmt2bubble (Cons y202 Nil) =
  Pair2
    P.False (Cons y202 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortBubSortIsSortsmt2bubble (Cons y202 (Cons y244 xs136)) =
  case y202 P.<= y244 of
    P.True ->
      case tip2015sortBubSortIsSortsmt2bubble (Cons y244 xs136) of
        Pair2 b27 zs19 -> Pair2 b27 (Cons y202 zs19)
    P.False ->
      case tip2015sortBubSortIsSortsmt2bubble (Cons y202 xs136) of
        Pair2 c10 ys81 -> Pair2 P.True (Cons y244 ys81)
tip2015sortBubSortIsSortsmt2bubsort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortBubSortIsSortsmt2bubsort x195 =
  case tip2015sortBubSortIsSortsmt2bubble x195 of
    Pair2 c11 ys82 ->
      case c11 of
        P.True -> tip2015sortBubSortIsSortsmt2bubsort ys82
        P.False -> x195
tip2015listzelemnubrsmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015listzelemnubrsmt2zelem x196 Nil = P.False
tip2015listzelemnubrsmt2zelem x196 (Cons z179 ys83) =
  (x196 P.== z179) P.|| (tip2015listzelemnubrsmt2zelem x196 ys83)
tip2015listzelemnubrsmt2zdeleteAll ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015listzelemnubrsmt2zdeleteAll x197 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015listzelemnubrsmt2zdeleteAll x197 (Cons z180 xs137) =
  case x197 P.== z180 of
    P.True -> tip2015listzelemnubrsmt2zdeleteAll x197 xs137
    P.False ->
      Cons z180 (tip2015listzelemnubrsmt2zdeleteAll x197 xs137)
tip2015listzelemnubrsmt2znub ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015listzelemnubrsmt2znub Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015listzelemnubrsmt2znub (Cons y203 xs138) =
  Cons
    y203
    (tip2015listzelemnubrsmt2zdeleteAll
       y203 (tip2015listzelemnubrsmt2znub xs138))
return :: a84 -> Grammarssimpexprunambig3smt2list a84
return x198 =
  Cons x198 (Nil :: Grammarssimpexprunambig3smt2list a84)
tip2015sortTSortSortssmt2zisaplannerprop78smt2sorted ::
  Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortTSortSortssmt2zisaplannerprop78smt2sorted Nil = P.True
tip2015sortTSortSortssmt2zisaplannerprop78smt2sorted
  (Cons y204 Nil) =
  P.True
tip2015sortTSortSortssmt2zisaplannerprop78smt2sorted
  (Cons y204 (Cons y245 xs139)) =
  (y204 P.<= y245) P.&&
    (tip2015sortTSortSortssmt2zisaplannerprop78smt2sorted
       (Cons y245 xs139))
tip2015sortTSortSortssmt2add ::
  P.Int ->
    Tip2015treesortAddSamesmt2Tree P.Int ->
      Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortTSortSortssmt2add
  x199 (Tip2015treesortAddSamesmt2Node p12 z181 q14) =
  case x199 P.<= z181 of
    P.True ->
      Tip2015treesortAddSamesmt2Node
        (tip2015sortTSortSortssmt2add x199 p12) z181 q14
    P.False ->
      Tip2015treesortAddSamesmt2Node
        p12 z181 (tip2015sortTSortSortssmt2add x199 q14)
tip2015sortTSortSortssmt2add x199 Tip2015treesortAddSamesmt2Nil =
  Tip2015treesortAddSamesmt2Node
    (Tip2015treesortAddSamesmt2Nil ::
       Tip2015treesortAddSamesmt2Tree P.Int)
    x199
    (Tip2015treesortAddSamesmt2Nil ::
       Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortTSortSortssmt2toTree ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortTSortSortssmt2toTree Nil =
  Tip2015treesortAddSamesmt2Nil ::
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortTSortSortssmt2toTree (Cons y205 xs140) =
  tip2015sortTSortSortssmt2add
    y205 (tip2015sortTSortSortssmt2toTree xs140)
tip2015sortTSortSortssmt2tsort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortTSortSortssmt2tsort x200 =
  tip2015treesortAddSamesmt2flatten
    (tip2015sortTSortSortssmt2toTree x200)
    (Nil :: Grammarssimpexprunambig3smt2list P.Int)
listDeleteMinimum ::
  Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
    Maybe (Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat)
listDeleteMinimum Nil =
  Nothing ::
    Maybe (Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat)
listDeleteMinimum (Cons y206 xs141) =
  Tip2015heapdeleteMinimumsmt2Just xs141
maybeToList ::
  Maybe Tip2015heapSortPermutessmt2Heap ->
    Maybe (Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat)
maybeToList Nothing =
  Nothing ::
    Maybe (Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat)
maybeToList (Tip2015heapdeleteMinimumsmt2Just y207) =
  Tip2015heapdeleteMinimumsmt2Just (toList2 y207)
tip2015heapdeleteMinimumsmt2deleteMinimum ::
  Tip2015heapSortPermutessmt2Heap ->
    Maybe Tip2015heapSortPermutessmt2Heap
tip2015heapdeleteMinimumsmt2deleteMinimum
  (Tip2015heapSortPermutessmt2Node l6 y208 r6) =
  Tip2015heapdeleteMinimumsmt2Just
    (tip2015heapSortPermutessmt2merge l6 r6)
tip2015heapdeleteMinimumsmt2deleteMinimum
  Tip2015heapSortPermutessmt2Nil =
  Nothing :: Maybe Tip2015heapSortPermutessmt2Heap
tip2015sortSSortCountsmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortCountsmt2zdelete x201 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortCountsmt2zdelete x201 (Cons z182 ys84) =
  case x201 P.== z182 of
    P.True -> ys84
    P.False -> Cons z182 (tip2015sortSSortCountsmt2zdelete x201 ys84)
tip2015sortSSortCountsmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015sortSSortCountsmt2zcount x202 Nil = Isaplannerprop54smt2Z
tip2015sortSSortCountsmt2zcount x202 (Cons z183 xs142) =
  case x202 P.== z183 of
    P.True ->
      Isaplannerprop54smt2S (tip2015sortSSortCountsmt2zcount x202 xs142)
    P.False -> tip2015sortSSortCountsmt2zcount x202 xs142
tip2015sortSSortCountsmt2ssortminimum ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Int
tip2015sortSSortCountsmt2ssortminimum x203 Nil = x203
tip2015sortSSortCountsmt2ssortminimum x203 (Cons z184 ys85) =
  case z184 P.<= x203 of
    P.True -> tip2015sortSSortCountsmt2ssortminimum z184 ys85
    P.False -> tip2015sortSSortCountsmt2ssortminimum x203 ys85
tip2015sortSSortCountsmt2ssort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortCountsmt2ssort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortSSortCountsmt2ssort (Cons y209 ys86) =
  let m11 = tip2015sortSSortCountsmt2ssortminimum y209 ys86
    in Cons
         m11
         (tip2015sortSSortCountsmt2ssort
            (tip2015sortSSortCountsmt2zdelete m11 (Cons y209 ys86)))
tip2015sortBubSortSortssmt2zisaplannerprop78smt2sorted ::
  Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortBubSortSortssmt2zisaplannerprop78smt2sorted Nil = P.True
tip2015sortBubSortSortssmt2zisaplannerprop78smt2sorted
  (Cons y246 Nil) =
  P.True
tip2015sortBubSortSortssmt2zisaplannerprop78smt2sorted
  (Cons y246 (Cons y247 xs143)) =
  (y246 P.<= y247) P.&&
    (tip2015sortBubSortSortssmt2zisaplannerprop78smt2sorted
       (Cons y247 xs143))
tip2015sortBubSortSortssmt2bubble ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Isaplannerprop45smt2Pair
      P.Bool (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortBubSortSortssmt2bubble Nil =
  Pair2 P.False (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortBubSortSortssmt2bubble (Cons y248 Nil) =
  Pair2
    P.False (Cons y248 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortBubSortSortssmt2bubble (Cons y248 (Cons y249 xs144)) =
  case y248 P.<= y249 of
    P.True ->
      case tip2015sortBubSortSortssmt2bubble (Cons y249 xs144) of
        Pair2 b28 zs20 -> Pair2 b28 (Cons y248 zs20)
    P.False ->
      case tip2015sortBubSortSortssmt2bubble (Cons y248 xs144) of
        Pair2 c12 ys87 -> Pair2 P.True (Cons y249 ys87)
tip2015sortBubSortSortssmt2bubsort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortBubSortSortssmt2bubsort x204 =
  case tip2015sortBubSortSortssmt2bubble x204 of
    Pair2 c13 ys88 ->
      case c13 of
        P.True -> tip2015sortBubSortSortssmt2bubsort ys88
        P.False -> x204
zero :: Tip2015intaddassocsmt2Integer
zero = Tip2015intaddassocsmt2P Isaplannerprop54smt2Z
neg ::
  Tip2015intaddassocsmt2Integer -> Tip2015intaddassocsmt2Integer
neg (Tip2015intaddassocsmt2P Isaplannerprop54smt2Z) =
  Tip2015intaddassocsmt2P Isaplannerprop54smt2Z
neg (Tip2015intaddassocsmt2P (Isaplannerprop54smt2S n11)) =
  Tip2015intaddassocsmt2N n11
neg (Tip2015intaddassocsmt2N m12) =
  Tip2015intaddassocsmt2P (Isaplannerprop54smt2S m12)
tip2015sortHSortIsSortsmt2toHeap2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list
      (Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortHSortIsSortsmt2toHeap2 Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortHSortIsSortsmt2toHeap2 (Cons y250 z185) =
  Cons
    (Tip2015treesortAddSamesmt2Node
       (Tip2015treesortAddSamesmt2Nil ::
          Tip2015treesortAddSamesmt2Tree P.Int)
       y250
       (Tip2015treesortAddSamesmt2Nil ::
          Tip2015treesortAddSamesmt2Tree P.Int))
    (tip2015sortHSortIsSortsmt2toHeap2 z185)
tip2015sortHSortIsSortsmt2insert2 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortHSortIsSortsmt2insert2 x205 Nil =
  Cons x205 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortHSortIsSortsmt2insert2 x205 (Cons z186 xs145) =
  case x205 P.<= z186 of
    P.True -> Cons x205 (Cons z186 xs145)
    P.False -> Cons z186 (tip2015sortHSortIsSortsmt2insert2 x205 xs145)
tip2015sortHSortIsSortsmt2isort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortHSortIsSortsmt2isort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortHSortIsSortsmt2isort (Cons y251 xs146) =
  tip2015sortHSortIsSortsmt2insert2
    y251 (tip2015sortHSortIsSortsmt2isort xs146)
tip2015sortHSortIsSortsmt2hmerge ::
  Tip2015treesortAddSamesmt2Tree P.Int ->
    Tip2015treesortAddSamesmt2Tree P.Int ->
      Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortHSortIsSortsmt2hmerge
  (Tip2015treesortAddSamesmt2Node z187 x272 x349)
  (Tip2015treesortAddSamesmt2Node x440 x516 x615) =
  case x272 P.<= x516 of
    P.True ->
      Tip2015treesortAddSamesmt2Node
        (tip2015sortHSortIsSortsmt2hmerge
           x349 (Tip2015treesortAddSamesmt2Node x440 x516 x615))
        x272 z187
    P.False ->
      Tip2015treesortAddSamesmt2Node
        (tip2015sortHSortIsSortsmt2hmerge
           (Tip2015treesortAddSamesmt2Node z187 x272 x349) x615)
        x516 x440
tip2015sortHSortIsSortsmt2hmerge
  (Tip2015treesortAddSamesmt2Node z187 x272 x349)
  Tip2015treesortAddSamesmt2Nil =
  Tip2015treesortAddSamesmt2Node z187 x272 x349
tip2015sortHSortIsSortsmt2hmerge
  Tip2015treesortAddSamesmt2Nil y252 =
  y252
tip2015sortHSortIsSortsmt2hpairwise ::
  Grammarssimpexprunambig3smt2list
    (Tip2015treesortAddSamesmt2Tree P.Int) ->
    Grammarssimpexprunambig3smt2list
      (Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortHSortIsSortsmt2hpairwise Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortHSortIsSortsmt2hpairwise (Cons p13 Nil) =
  Cons
    p13
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Tip2015treesortAddSamesmt2Tree P.Int))
tip2015sortHSortIsSortsmt2hpairwise (Cons p13 (Cons q15 rs)) =
  Cons
    (tip2015sortHSortIsSortsmt2hmerge p13 q15)
    (tip2015sortHSortIsSortsmt2hpairwise rs)
tip2015sortHSortIsSortsmt2hmerging ::
  Grammarssimpexprunambig3smt2list
    (Tip2015treesortAddSamesmt2Tree P.Int) ->
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortHSortIsSortsmt2hmerging Nil =
  Tip2015treesortAddSamesmt2Nil ::
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortHSortIsSortsmt2hmerging (Cons p14 Nil) = p14
tip2015sortHSortIsSortsmt2hmerging (Cons p14 (Cons z188 x273)) =
  tip2015sortHSortIsSortsmt2hmerging
    (tip2015sortHSortIsSortsmt2hpairwise (Cons p14 (Cons z188 x273)))
tip2015sortHSortIsSortsmt2toHeap ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortHSortIsSortsmt2toHeap x206 =
  tip2015sortHSortIsSortsmt2hmerging
    (tip2015sortHSortIsSortsmt2toHeap2 x206)
tip2015sortHSortIsSortsmt2toList ::
  Tip2015treesortAddSamesmt2Tree P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortHSortIsSortsmt2toList
  (Tip2015treesortAddSamesmt2Node p15 y253 q16) =
  Cons
    y253
    (tip2015sortHSortIsSortsmt2toList
       (tip2015sortHSortIsSortsmt2hmerge p15 q16))
tip2015sortHSortIsSortsmt2toList Tip2015treesortAddSamesmt2Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortHSortIsSortsmt2hsort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortHSortIsSortsmt2hsort x207 =
  tip2015sortHSortIsSortsmt2toList
    (tip2015sortHSortIsSortsmt2toHeap x207)
tip2015sortNStoogeSortIsSortsmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortIsSortsmt2sort2 x208 y254 =
  case x208 P.<= y254 of
    P.True ->
      Cons
        x208 (Cons y254 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y254 (Cons x208 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortNStoogeSortIsSortsmt2insert2 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortIsSortsmt2insert2 x209 Nil =
  Cons x209 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortNStoogeSortIsSortsmt2insert2 x209 (Cons z189 xs147) =
  case x209 P.<= z189 of
    P.True -> Cons x209 (Cons z189 xs147)
    P.False ->
      Cons z189 (tip2015sortNStoogeSortIsSortsmt2insert2 x209 xs147)
tip2015sortNStoogeSortIsSortsmt2isort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortIsSortsmt2isort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortIsSortsmt2isort (Cons y255 xs148) =
  tip2015sortNStoogeSortIsSortsmt2insert2
    y255 (tip2015sortNStoogeSortIsSortsmt2isort xs148)
tip2015sortNStoogeSortIsSortsmt2nstooge1sort2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortIsSortsmt2nstooge1sort2 x274 =
  case tip2015sortNStoogeSort2Countsmt2splitAt
         (third (isaplannerprop68smt2len x274))
         (isaplannerprop85smt2rev x274) of
    Pair2 ys89 zs21 ->
      append
        (tip2015sortNStoogeSortIsSortsmt2nstoogesort zs21)
        (isaplannerprop85smt2rev ys89)
tip2015sortNStoogeSortIsSortsmt2nstoogesort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortIsSortsmt2nstoogesort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortIsSortsmt2nstoogesort (Cons y256 Nil) =
  Cons y256 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortNStoogeSortIsSortsmt2nstoogesort
  (Cons y256 (Cons y257 Nil)) =
  tip2015sortNStoogeSortIsSortsmt2sort2 y256 y257
tip2015sortNStoogeSortIsSortsmt2nstoogesort
  (Cons y256 (Cons y257 (Cons x350 x441))) =
  tip2015sortNStoogeSortIsSortsmt2nstooge1sort2
    (tip2015sortNStoogeSortIsSortsmt2nstooge1sort1
       (tip2015sortNStoogeSortIsSortsmt2nstooge1sort2
          (Cons y256 (Cons y257 (Cons x350 x441)))))
tip2015sortNStoogeSortIsSortsmt2nstooge1sort1 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortIsSortsmt2nstooge1sort1 x275 =
  case tip2015sortNStoogeSort2Countsmt2splitAt
         (third (isaplannerprop68smt2len x275)) x275 of
    Pair2 ys90 zs22 ->
      append ys90 (tip2015sortNStoogeSortIsSortsmt2nstoogesort zs22)
tip2015sortNMSortTDCountsmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015sortNMSortTDCountsmt2zcount x276 Nil = Isaplannerprop54smt2Z
tip2015sortNMSortTDCountsmt2zcount x276 (Cons z190 xs149) =
  case x276 P.== z190 of
    P.True ->
      Isaplannerprop54smt2S
        (tip2015sortNMSortTDCountsmt2zcount x276 xs149)
    P.False -> tip2015sortNMSortTDCountsmt2zcount x276 xs149
tip2015sortNMSortTDCountsmt2lmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortNMSortTDCountsmt2lmerge Nil y258 = y258
tip2015sortNMSortTDCountsmt2lmerge (Cons z191 x277) Nil =
  Cons z191 x277
tip2015sortNMSortTDCountsmt2lmerge
  (Cons z191 x277) (Cons x351 x442) =
  case z191 P.<= x351 of
    P.True ->
      Cons
        z191 (tip2015sortNMSortTDCountsmt2lmerge x277 (Cons x351 x442))
    P.False ->
      Cons
        x351 (tip2015sortNMSortTDCountsmt2lmerge (Cons z191 x277) x442)
tip2015sortNMSortTDCountsmt2nmsorttd ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNMSortTDCountsmt2nmsorttd Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNMSortTDCountsmt2nmsorttd (Cons y259 Nil) =
  Cons y259 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortNMSortTDCountsmt2nmsorttd (Cons y259 (Cons x278 x352)) =
  let k5 =
        half (isaplannerprop68smt2len (Cons y259 (Cons x278 x352)))
    in tip2015sortNMSortTDCountsmt2lmerge
         (tip2015sortNMSortTDCountsmt2nmsorttd
            (isaplannerprop82smt2take k5 (Cons y259 (Cons x278 x352))))
         (tip2015sortNMSortTDCountsmt2nmsorttd
            (isaplannerprop12smt2drop k5 (Cons y259 (Cons x278 x352))))
tip2015natboringgtirreflexivesmt2gt ::
  Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat -> P.Bool
tip2015natboringgtirreflexivesmt2gt Isaplannerprop54smt2Z y260 =
  P.False
tip2015natboringgtirreflexivesmt2gt
  (Isaplannerprop54smt2S z192) Isaplannerprop54smt2Z =
  P.True
tip2015natboringgtirreflexivesmt2gt
  (Isaplannerprop54smt2S z192) (Isaplannerprop54smt2S x279) =
  tip2015natboringgtirreflexivesmt2gt z192 x279
tip2015sortStoogeSortCountsmt2ztake ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a85 ->
      Grammarssimpexprunambig3smt2list a85
tip2015sortStoogeSortCountsmt2ztake x280 y261 =
  case x280 P.== (0) of
    P.True -> Nil :: Grammarssimpexprunambig3smt2list a85
    P.False ->
      case y261 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a85
        Cons z193 xs150 ->
          Cons
            z193 (tip2015sortStoogeSortCountsmt2ztake (x280 P.- (1)) xs150)
tip2015sortStoogeSortCountsmt2zlength ::
  Grammarssimpexprunambig3smt2list a86 -> P.Int
tip2015sortStoogeSortCountsmt2zlength Nil = 0
tip2015sortStoogeSortCountsmt2zlength (Cons y262 xs151) =
  (1) P.+ (tip2015sortStoogeSortCountsmt2zlength xs151)
tip2015sortStoogeSortCountsmt2zdrop ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a87 ->
      Grammarssimpexprunambig3smt2list a87
tip2015sortStoogeSortCountsmt2zdrop x281 y263 =
  case x281 P.== (0) of
    P.True -> y263
    P.False ->
      case y263 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a87
        Cons z194 xs152 ->
          tip2015sortStoogeSortCountsmt2zdrop (x281 P.- (1)) xs152
tip2015sortStoogeSortCountsmt2zsplitAt ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a88 ->
      Isaplannerprop45smt2Pair
        (Grammarssimpexprunambig3smt2list a88)
        (Grammarssimpexprunambig3smt2list a88)
tip2015sortStoogeSortCountsmt2zsplitAt x282 y264 =
  Pair2
    (tip2015sortStoogeSortCountsmt2ztake x282 y264)
    (tip2015sortStoogeSortCountsmt2zdrop x282 y264)
tip2015sortStoogeSortCountsmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015sortStoogeSortCountsmt2zcount x283 Nil =
  Isaplannerprop54smt2Z
tip2015sortStoogeSortCountsmt2zcount x283 (Cons z195 xs153) =
  case x283 P.== z195 of
    P.True ->
      Isaplannerprop54smt2S
        (tip2015sortStoogeSortCountsmt2zcount x283 xs153)
    P.False -> tip2015sortStoogeSortCountsmt2zcount x283 xs153
tip2015sortStoogeSortCountsmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortCountsmt2sort2 x284 y265 =
  case x284 P.<= y265 of
    P.True ->
      Cons
        x284 (Cons y265 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y265 (Cons x284 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortStoogeSortCountsmt2stooge1sort2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortCountsmt2stooge1sort2 x285 =
  case tip2015sortStoogeSortCountsmt2zsplitAt
         (P.div (tip2015sortStoogeSortCountsmt2zlength x285) (3))
         (isaplannerprop85smt2rev x285) of
    Pair2 ys91 zs23 ->
      append
        (tip2015sortStoogeSortCountsmt2stoogesort zs23)
        (isaplannerprop85smt2rev ys91)
tip2015sortStoogeSortCountsmt2stoogesort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortCountsmt2stoogesort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortCountsmt2stoogesort (Cons y266 Nil) =
  Cons y266 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortStoogeSortCountsmt2stoogesort
  (Cons y266 (Cons y267 Nil)) =
  tip2015sortStoogeSortCountsmt2sort2 y266 y267
tip2015sortStoogeSortCountsmt2stoogesort
  (Cons y266 (Cons y267 (Cons x353 x443))) =
  tip2015sortStoogeSortCountsmt2stooge1sort2
    (tip2015sortStoogeSortCountsmt2stooge1sort1
       (tip2015sortStoogeSortCountsmt2stooge1sort2
          (Cons y266 (Cons y267 (Cons x353 x443)))))
tip2015sortStoogeSortCountsmt2stooge1sort1 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortCountsmt2stooge1sort1 x286 =
  case tip2015sortStoogeSortCountsmt2zsplitAt
         (P.div (tip2015sortStoogeSortCountsmt2zlength x286) (3)) x286 of
    Pair2 ys92 zs24 ->
      append ys92 (tip2015sortStoogeSortCountsmt2stoogesort zs24)
tip2015sortStoogeSort2Countsmt2ztake ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a89 ->
      Grammarssimpexprunambig3smt2list a89
tip2015sortStoogeSort2Countsmt2ztake x287 y268 =
  case x287 P.== (0) of
    P.True -> Nil :: Grammarssimpexprunambig3smt2list a89
    P.False ->
      case y268 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a89
        Cons z196 xs154 ->
          Cons
            z196 (tip2015sortStoogeSort2Countsmt2ztake (x287 P.- (1)) xs154)
tip2015sortStoogeSort2Countsmt2zlength ::
  Grammarssimpexprunambig3smt2list a90 -> P.Int
tip2015sortStoogeSort2Countsmt2zlength Nil = 0
tip2015sortStoogeSort2Countsmt2zlength (Cons y269 xs155) =
  (1) P.+ (tip2015sortStoogeSort2Countsmt2zlength xs155)
tip2015sortStoogeSort2Countsmt2zdrop ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a91 ->
      Grammarssimpexprunambig3smt2list a91
tip2015sortStoogeSort2Countsmt2zdrop x288 y270 =
  case x288 P.== (0) of
    P.True -> y270
    P.False ->
      case y270 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a91
        Cons z197 xs156 ->
          tip2015sortStoogeSort2Countsmt2zdrop (x288 P.- (1)) xs156
tip2015sortStoogeSort2Countsmt2zsplitAt ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a92 ->
      Isaplannerprop45smt2Pair
        (Grammarssimpexprunambig3smt2list a92)
        (Grammarssimpexprunambig3smt2list a92)
tip2015sortStoogeSort2Countsmt2zsplitAt x289 y271 =
  Pair2
    (tip2015sortStoogeSort2Countsmt2ztake x289 y271)
    (tip2015sortStoogeSort2Countsmt2zdrop x289 y271)
tip2015sortStoogeSort2Countsmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015sortStoogeSort2Countsmt2zcount x290 Nil =
  Isaplannerprop54smt2Z
tip2015sortStoogeSort2Countsmt2zcount x290 (Cons z198 xs157) =
  case x290 P.== z198 of
    P.True ->
      Isaplannerprop54smt2S
        (tip2015sortStoogeSort2Countsmt2zcount x290 xs157)
    P.False -> tip2015sortStoogeSort2Countsmt2zcount x290 xs157
tip2015sortStoogeSort2Countsmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSort2Countsmt2sort2 x291 y272 =
  case x291 P.<= y272 of
    P.True ->
      Cons
        x291 (Cons y272 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y272 (Cons x291 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortNStoogeSort2IsSortsmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2IsSortsmt2sort2 x292 y273 =
  case x292 P.<= y273 of
    P.True ->
      Cons
        x292 (Cons y273 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y273 (Cons x292 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortNStoogeSort2IsSortsmt2insert2 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2IsSortsmt2insert2 x293 Nil =
  Cons x293 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortNStoogeSort2IsSortsmt2insert2 x293 (Cons z199 xs158) =
  case x293 P.<= z199 of
    P.True -> Cons x293 (Cons z199 xs158)
    P.False ->
      Cons z199 (tip2015sortNStoogeSort2IsSortsmt2insert2 x293 xs158)
tip2015sortNStoogeSort2IsSortsmt2isort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2IsSortsmt2isort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2IsSortsmt2isort (Cons y274 xs159) =
  tip2015sortNStoogeSort2IsSortsmt2insert2
    y274 (tip2015sortNStoogeSort2IsSortsmt2isort xs159)
tip2015sortNStoogeSort2IsSortsmt2nstooge2sort2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2IsSortsmt2nstooge2sort2 x294 =
  case tip2015sortNStoogeSort2Countsmt2splitAt
         (twoThirds (isaplannerprop68smt2len x294)) x294 of
    Pair2 ys93 zs25 ->
      append (tip2015sortNStoogeSort2IsSortsmt2nstoogesort2 ys93) zs25
tip2015sortNStoogeSort2IsSortsmt2nstoogesort2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2IsSortsmt2nstoogesort2 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2IsSortsmt2nstoogesort2 (Cons y275 Nil) =
  Cons y275 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortNStoogeSort2IsSortsmt2nstoogesort2
  (Cons y275 (Cons y276 Nil)) =
  tip2015sortNStoogeSort2IsSortsmt2sort2 y275 y276
tip2015sortNStoogeSort2IsSortsmt2nstoogesort2
  (Cons y275 (Cons y276 (Cons x354 x444))) =
  tip2015sortNStoogeSort2IsSortsmt2nstooge2sort2
    (tip2015sortNStoogeSort2IsSortsmt2nstooge2sort1
       (tip2015sortNStoogeSort2IsSortsmt2nstooge2sort2
          (Cons y275 (Cons y276 (Cons x354 x444)))))
tip2015sortNStoogeSort2IsSortsmt2nstooge2sort1 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSort2IsSortsmt2nstooge2sort1 x295 =
  case tip2015sortNStoogeSort2Countsmt2splitAt
         (third (isaplannerprop68smt2len x295)) x295 of
    Pair2 ys94 zs26 ->
      append ys94 (tip2015sortNStoogeSort2IsSortsmt2nstoogesort2 zs26)
tip2015treeSwapABsmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015treeSwapABsmt2zelem x296 Nil = P.False
tip2015treeSwapABsmt2zelem x296 (Cons z200 ys95) =
  (x296 P.== z200) P.|| (tip2015treeSwapABsmt2zelem x296 ys95)
swap ::
  P.Int ->
    P.Int ->
      Tip2015treesortAddSamesmt2Tree P.Int ->
        Tip2015treesortAddSamesmt2Tree P.Int
swap x297 y277 (Tip2015treesortAddSamesmt2Node p16 x298 q17) =
  case x298 P.== x297 of
    P.True ->
      Tip2015treesortAddSamesmt2Node
        (swap x297 y277 p16) y277 (swap x297 y277 q17)
    P.False ->
      case x298 P.== y277 of
        P.True ->
          Tip2015treesortAddSamesmt2Node
            (swap x297 y277 p16) x297 (swap x297 y277 q17)
        P.False ->
          Tip2015treesortAddSamesmt2Node
            (swap x297 y277 p16) x298 (swap x297 y277 q17)
swap x297 y277 Tip2015treesortAddSamesmt2Nil =
  Tip2015treesortAddSamesmt2Nil ::
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015treesortSortPermutesticksmt2toTree ::
  Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
    Tip2015treesortAddSamesmt2Tree Isaplannerprop54smt2Nat
tip2015treesortSortPermutesticksmt2toTree Nil =
  Tip2015treesortAddSamesmt2Nil ::
    Tip2015treesortAddSamesmt2Tree Isaplannerprop54smt2Nat
tip2015treesortSortPermutesticksmt2toTree (Cons y278 xs160) =
  tip2015treesortAddSamesmt2add
    y278 (tip2015treesortSortPermutesticksmt2toTree xs160)
tip2015treesortSortPermutesticksmt2tsort ::
  Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
tip2015treesortSortPermutesticksmt2tsort x299 =
  tip2015treesortAddSamesmt2flatten
    (tip2015treesortSortPermutesticksmt2toTree x299)
    (Nil :: Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat)
tip2015sortNStoogeSortPermutessmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortNStoogeSortPermutessmt2zelem x300 Nil = P.False
tip2015sortNStoogeSortPermutessmt2zelem x300 (Cons z201 ys96) =
  (x300 P.== z201) P.||
    (tip2015sortNStoogeSortPermutessmt2zelem x300 ys96)
tip2015sortNStoogeSortPermutessmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortPermutessmt2zdelete x301 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortPermutessmt2zdelete x301 (Cons z202 ys97) =
  case x301 P.== z202 of
    P.True -> ys97
    P.False ->
      Cons z202 (tip2015sortNStoogeSortPermutessmt2zdelete x301 ys97)
tip2015sortNStoogeSortPermutessmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortPermutessmt2sort2 x302 y279 =
  case x302 P.<= y279 of
    P.True ->
      Cons
        x302 (Cons y279 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y279 (Cons x302 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortNStoogeSortPermutessmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortNStoogeSortPermutessmt2zisPermutation Nil y280 =
  null y280
tip2015sortNStoogeSortPermutessmt2zisPermutation
  (Cons z203 xs161) y280 =
  (tip2015sortNStoogeSortPermutessmt2zelem z203 y280) P.&&
    (tip2015sortNStoogeSortPermutessmt2zisPermutation
       xs161 (tip2015sortNStoogeSortPermutessmt2zdelete z203 y280))
tip2015sortNStoogeSortPermutessmt2nstooge1sort2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortPermutessmt2nstooge1sort2 x303 =
  case tip2015sortNStoogeSort2Countsmt2splitAt
         (third (isaplannerprop68smt2len x303))
         (isaplannerprop85smt2rev x303) of
    Pair2 ys98 zs27 ->
      append
        (tip2015sortNStoogeSortPermutessmt2nstoogesort zs27)
        (isaplannerprop85smt2rev ys98)
tip2015sortNStoogeSortPermutessmt2nstoogesort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortPermutessmt2nstoogesort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortPermutessmt2nstoogesort (Cons y281 Nil) =
  Cons y281 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortNStoogeSortPermutessmt2nstoogesort
  (Cons y281 (Cons y282 Nil)) =
  tip2015sortNStoogeSortPermutessmt2sort2 y281 y282
tip2015sortNStoogeSortPermutessmt2nstoogesort
  (Cons y281 (Cons y282 (Cons x355 x445))) =
  tip2015sortNStoogeSortPermutessmt2nstooge1sort2
    (tip2015sortNStoogeSortPermutessmt2nstooge1sort1
       (tip2015sortNStoogeSortPermutessmt2nstooge1sort2
          (Cons y281 (Cons y282 (Cons x355 x445)))))
tip2015sortNStoogeSortPermutessmt2nstooge1sort1 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNStoogeSortPermutessmt2nstooge1sort1 x304 =
  case tip2015sortNStoogeSort2Countsmt2splitAt
         (third (isaplannerprop68smt2len x304)) x304 of
    Pair2 ys99 zs28 ->
      append ys99 (tip2015sortNStoogeSortPermutessmt2nstoogesort zs28)
tip2015sortHSortPermutessmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortHSortPermutessmt2zelem x305 Nil = P.False
tip2015sortHSortPermutessmt2zelem x305 (Cons z204 ys100) =
  (x305 P.== z204) P.||
    (tip2015sortHSortPermutessmt2zelem x305 ys100)
tip2015sortHSortPermutessmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortHSortPermutessmt2zdelete x306 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortHSortPermutessmt2zdelete x306 (Cons z205 ys101) =
  case x306 P.== z205 of
    P.True -> ys101
    P.False ->
      Cons z205 (tip2015sortHSortPermutessmt2zdelete x306 ys101)
tip2015sortHSortPermutessmt2toHeap2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list
      (Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortHSortPermutessmt2toHeap2 Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortHSortPermutessmt2toHeap2 (Cons y283 z206) =
  Cons
    (Tip2015treesortAddSamesmt2Node
       (Tip2015treesortAddSamesmt2Nil ::
          Tip2015treesortAddSamesmt2Tree P.Int)
       y283
       (Tip2015treesortAddSamesmt2Nil ::
          Tip2015treesortAddSamesmt2Tree P.Int))
    (tip2015sortHSortPermutessmt2toHeap2 z206)
tip2015sortHSortPermutessmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortHSortPermutessmt2zisPermutation Nil y284 = null y284
tip2015sortHSortPermutessmt2zisPermutation (Cons z207 xs162) y284 =
  (tip2015sortHSortPermutessmt2zelem z207 y284) P.&&
    (tip2015sortHSortPermutessmt2zisPermutation
       xs162 (tip2015sortHSortPermutessmt2zdelete z207 y284))
tip2015sortHSortPermutessmt2hmerge ::
  Tip2015treesortAddSamesmt2Tree P.Int ->
    Tip2015treesortAddSamesmt2Tree P.Int ->
      Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortHSortPermutessmt2hmerge
  (Tip2015treesortAddSamesmt2Node z208 x2100 x356)
  (Tip2015treesortAddSamesmt2Node x446 x517 x616) =
  case x2100 P.<= x517 of
    P.True ->
      Tip2015treesortAddSamesmt2Node
        (tip2015sortHSortPermutessmt2hmerge
           x356 (Tip2015treesortAddSamesmt2Node x446 x517 x616))
        x2100 z208
    P.False ->
      Tip2015treesortAddSamesmt2Node
        (tip2015sortHSortPermutessmt2hmerge
           (Tip2015treesortAddSamesmt2Node z208 x2100 x356) x616)
        x517 x446
tip2015sortHSortPermutessmt2hmerge
  (Tip2015treesortAddSamesmt2Node z208 x2100 x356)
  Tip2015treesortAddSamesmt2Nil =
  Tip2015treesortAddSamesmt2Node z208 x2100 x356
tip2015sortHSortPermutessmt2hmerge
  Tip2015treesortAddSamesmt2Nil y285 =
  y285
tip2015sortHSortPermutessmt2hpairwise ::
  Grammarssimpexprunambig3smt2list
    (Tip2015treesortAddSamesmt2Tree P.Int) ->
    Grammarssimpexprunambig3smt2list
      (Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortHSortPermutessmt2hpairwise Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortHSortPermutessmt2hpairwise (Cons p17 Nil) =
  Cons
    p17
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Tip2015treesortAddSamesmt2Tree P.Int))
tip2015sortHSortPermutessmt2hpairwise (Cons p17 (Cons q18 qs2)) =
  Cons
    (tip2015sortHSortPermutessmt2hmerge p17 q18)
    (tip2015sortHSortPermutessmt2hpairwise qs2)
tip2015sortHSortPermutessmt2hmerging ::
  Grammarssimpexprunambig3smt2list
    (Tip2015treesortAddSamesmt2Tree P.Int) ->
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortHSortPermutessmt2hmerging Nil =
  Tip2015treesortAddSamesmt2Nil ::
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortHSortPermutessmt2hmerging (Cons p18 Nil) = p18
tip2015sortHSortPermutessmt2hmerging (Cons p18 (Cons z209 x2101)) =
  tip2015sortHSortPermutessmt2hmerging
    (tip2015sortHSortPermutessmt2hpairwise
       (Cons p18 (Cons z209 x2101)))
tip2015sortHSortPermutessmt2toHeap ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortHSortPermutessmt2toHeap x307 =
  tip2015sortHSortPermutessmt2hmerging
    (tip2015sortHSortPermutessmt2toHeap2 x307)
tip2015sortHSortPermutessmt2toList ::
  Tip2015treesortAddSamesmt2Tree P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortHSortPermutessmt2toList
  (Tip2015treesortAddSamesmt2Node p19 y286 q19) =
  Cons
    y286
    (tip2015sortHSortPermutessmt2toList
       (tip2015sortHSortPermutessmt2hmerge p19 q19))
tip2015sortHSortPermutessmt2toList Tip2015treesortAddSamesmt2Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortHSortPermutessmt2hsort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortHSortPermutessmt2hsort x308 =
  tip2015sortHSortPermutessmt2toList
    (tip2015sortHSortPermutessmt2toHeap x308)
removeOne2 ::
  GrammarspackratunambigPackratsmt2Tok ->
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list
         GrammarspackratunambigPackratsmt2Tok) ->
      Grammarssimpexprunambig3smt2list
        (Grammarssimpexprunambig3smt2list
           GrammarspackratunambigPackratsmt2Tok)
removeOne2 x309 Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list
         GrammarspackratunambigPackratsmt2Tok)
removeOne2 x309 (Cons z211 x2102) =
  Cons (Cons x309 z211) (removeOne2 x309 x2102)
tip2015relaxedprefixcorrectsmt2removeOne ::
  Grammarssimpexprunambig3smt2list
    GrammarspackratunambigPackratsmt2Tok ->
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list
         GrammarspackratunambigPackratsmt2Tok)
tip2015relaxedprefixcorrectsmt2removeOne Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list
         GrammarspackratunambigPackratsmt2Tok)
tip2015relaxedprefixcorrectsmt2removeOne (Cons y287 xs163) =
  Cons
    xs163
    (removeOne2 y287 (tip2015relaxedprefixcorrectsmt2removeOne xs163))
spec2 ::
  Grammarssimpexprunambig3smt2list
    GrammarspackratunambigPackratsmt2Tok ->
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list
         GrammarspackratunambigPackratsmt2Tok) ->
      Grammarssimpexprunambig3smt2list P.Bool
spec2 ys102 Nil = Nil :: Grammarssimpexprunambig3smt2list P.Bool
spec2 ys102 (Cons y288 z212) =
  Cons (isPrefix y288 ys102) (spec2 ys102 z212)
tip2015sortTSortPermutessmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortTSortPermutessmt2zelem x357 Nil = P.False
tip2015sortTSortPermutessmt2zelem x357 (Cons z213 ys103) =
  (x357 P.== z213) P.||
    (tip2015sortTSortPermutessmt2zelem x357 ys103)
tip2015sortTSortPermutessmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortTSortPermutessmt2zdelete x358 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortTSortPermutessmt2zdelete x358 (Cons z214 ys104) =
  case x358 P.== z214 of
    P.True -> ys104
    P.False ->
      Cons z214 (tip2015sortTSortPermutessmt2zdelete x358 ys104)
tip2015sortTSortPermutessmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortTSortPermutessmt2zisPermutation Nil y289 = null y289
tip2015sortTSortPermutessmt2zisPermutation (Cons z215 xs164) y289 =
  (tip2015sortTSortPermutessmt2zelem z215 y289) P.&&
    (tip2015sortTSortPermutessmt2zisPermutation
       xs164 (tip2015sortTSortPermutessmt2zdelete z215 y289))
tip2015sortTSortPermutessmt2add ::
  P.Int ->
    Tip2015treesortAddSamesmt2Tree P.Int ->
      Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortTSortPermutessmt2add
  x359 (Tip2015treesortAddSamesmt2Node p20 z216 q20) =
  case x359 P.<= z216 of
    P.True ->
      Tip2015treesortAddSamesmt2Node
        (tip2015sortTSortPermutessmt2add x359 p20) z216 q20
    P.False ->
      Tip2015treesortAddSamesmt2Node
        p20 z216 (tip2015sortTSortPermutessmt2add x359 q20)
tip2015sortTSortPermutessmt2add
  x359 Tip2015treesortAddSamesmt2Nil =
  Tip2015treesortAddSamesmt2Node
    (Tip2015treesortAddSamesmt2Nil ::
       Tip2015treesortAddSamesmt2Tree P.Int)
    x359
    (Tip2015treesortAddSamesmt2Nil ::
       Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortTSortPermutessmt2toTree ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortTSortPermutessmt2toTree Nil =
  Tip2015treesortAddSamesmt2Nil ::
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortTSortPermutessmt2toTree (Cons y290 xs165) =
  tip2015sortTSortPermutessmt2add
    y290 (tip2015sortTSortPermutessmt2toTree xs165)
tip2015sortTSortPermutessmt2tsort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortTSortPermutessmt2tsort x360 =
  tip2015treesortAddSamesmt2flatten
    (tip2015sortTSortPermutessmt2toTree x360)
    (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015listzpermreflsmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015listzpermreflsmt2zelem x361 Nil = P.False
tip2015listzpermreflsmt2zelem x361 (Cons z217 ys105) =
  (x361 P.== z217) P.|| (tip2015listzpermreflsmt2zelem x361 ys105)
tip2015listzpermreflsmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015listzpermreflsmt2zdelete x362 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015listzpermreflsmt2zdelete x362 (Cons z218 ys106) =
  case x362 P.== z218 of
    P.True -> ys106
    P.False -> Cons z218 (tip2015listzpermreflsmt2zdelete x362 ys106)
tip2015listzpermreflsmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015listzpermreflsmt2zisPermutation Nil y291 = null y291
tip2015listzpermreflsmt2zisPermutation (Cons z219 xs166) y291 =
  (tip2015listzpermreflsmt2zelem z219 y291) P.&&
    (tip2015listzpermreflsmt2zisPermutation
       xs166 (tip2015listzpermreflsmt2zdelete z219 y291))
tip2015substSubstFreeNosmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015substSubstFreeNosmt2zelem x363 Nil = P.False
tip2015substSubstFreeNosmt2zelem x363 (Cons z220 ys107) =
  (x363 P.== z220) P.|| (tip2015substSubstFreeNosmt2zelem x363 ys107)
tip2015substSubstFreeNosmt2newmaximum ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Int
tip2015substSubstFreeNosmt2newmaximum x364 Nil = x364
tip2015substSubstFreeNosmt2newmaximum x364 (Cons z221 ys108) =
  case x364 P.<= z221 of
    P.True -> tip2015substSubstFreeNosmt2newmaximum z221 ys108
    P.False -> tip2015substSubstFreeNosmt2newmaximum x364 ys108
tip2015substSubstFreeNosmt2new ::
  Grammarssimpexprunambig3smt2list P.Int -> P.Int
tip2015substSubstFreeNosmt2new x365 =
  (tip2015substSubstFreeNosmt2newmaximum (0) x365) P.+ (1)
tip2015substSubstFreeNosmt2free ::
  Tip2015substSubstFreeNosmt2Expr ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015substSubstFreeNosmt2free
  (Tip2015substSubstFreeNosmt2Var y292) =
  Cons y292 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015substSubstFreeNosmt2free
  (Tip2015substSubstFreeNosmt2Lam z222 b17) =
  filter
    (\ x2103 -> z222 P./= x2103) (tip2015substSubstFreeNosmt2free b17)
tip2015substSubstFreeNosmt2free
  (Tip2015substSubstFreeNosmt2App a212 b29) =
  append
    (tip2015substSubstFreeNosmt2free a212)
    (tip2015substSubstFreeNosmt2free b29)
tip2015substSubstFreeNosmt2subst ::
  P.Int ->
    Tip2015substSubstFreeNosmt2Expr ->
      Tip2015substSubstFreeNosmt2Expr -> Tip2015substSubstFreeNosmt2Expr
tip2015substSubstFreeNosmt2subst
  x366 y293 (Tip2015substSubstFreeNosmt2Var y294) =
  case x366 P.== y294 of
    P.True -> y293
    P.False -> Tip2015substSubstFreeNosmt2Var y294
tip2015substSubstFreeNosmt2subst
  x366 y293 (Tip2015substSubstFreeNosmt2Lam y311 a93) =
  let z223 =
        tip2015substSubstFreeNosmt2new
          (append
             (tip2015substSubstFreeNosmt2free y293)
             (tip2015substSubstFreeNosmt2free a93))
    in case x366 P.== y311 of
         P.True -> Tip2015substSubstFreeNosmt2Lam y311 a93
         P.False ->
           case tip2015substSubstFreeNosmt2zelem
                  y311 (tip2015substSubstFreeNosmt2free y293) of
             P.True ->
               tip2015substSubstFreeNosmt2subst
                 x366 y293
                 (Tip2015substSubstFreeNosmt2Lam
                    z223
                    (tip2015substSubstFreeNosmt2subst
                       y311 (Tip2015substSubstFreeNosmt2Var z223) a93))
             P.False ->
               Tip2015substSubstFreeNosmt2Lam
                 y311 (tip2015substSubstFreeNosmt2subst x366 y293 a93)
tip2015substSubstFreeNosmt2subst
  x366 y293 (Tip2015substSubstFreeNosmt2App c14 b210) =
  Tip2015substSubstFreeNosmt2App
    (tip2015substSubstFreeNosmt2subst x366 y293 c14)
    (tip2015substSubstFreeNosmt2subst x366 y293 b210)
snd :: Isaplannerprop45smt2Pair a94 b18 -> b18
snd (Pair2 y295 z224) = z224
tip2015listPairOddssmt2evens ::
  Grammarssimpexprunambig3smt2list a95 ->
    Grammarssimpexprunambig3smt2list a95
tip2015listPairOddssmt2evens Nil =
  Nil :: Grammarssimpexprunambig3smt2list a95
tip2015listPairOddssmt2evens (Cons y296 xs167) =
  Cons y296 (tip2015listPairOddssmt2odds xs167)
tip2015listPairOddssmt2odds ::
  Grammarssimpexprunambig3smt2list a96 ->
    Grammarssimpexprunambig3smt2list a96
tip2015listPairOddssmt2odds Nil =
  Nil :: Grammarssimpexprunambig3smt2list a96
tip2015listPairOddssmt2odds (Cons y297 xs168) =
  tip2015listPairOddssmt2evens xs168
factorial :: Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
factorial Isaplannerprop54smt2Z =
  Isaplannerprop54smt2S Isaplannerprop54smt2Z
factorial (Isaplannerprop54smt2S n12) =
  tip2015nataltmulsamesmt2mult
    (Isaplannerprop54smt2S n12) (factorial n12)
tip2015sortHSortCountsmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015sortHSortCountsmt2zcount x367 Nil = Isaplannerprop54smt2Z
tip2015sortHSortCountsmt2zcount x367 (Cons z225 xs169) =
  case x367 P.== z225 of
    P.True ->
      Isaplannerprop54smt2S (tip2015sortHSortCountsmt2zcount x367 xs169)
    P.False -> tip2015sortHSortCountsmt2zcount x367 xs169
tip2015sortHSortCountsmt2toHeap2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list
      (Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortHSortCountsmt2toHeap2 Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortHSortCountsmt2toHeap2 (Cons y298 z226) =
  Cons
    (Tip2015treesortAddSamesmt2Node
       (Tip2015treesortAddSamesmt2Nil ::
          Tip2015treesortAddSamesmt2Tree P.Int)
       y298
       (Tip2015treesortAddSamesmt2Nil ::
          Tip2015treesortAddSamesmt2Tree P.Int))
    (tip2015sortHSortCountsmt2toHeap2 z226)
tip2015sortHSortCountsmt2hmerge ::
  Tip2015treesortAddSamesmt2Tree P.Int ->
    Tip2015treesortAddSamesmt2Tree P.Int ->
      Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortHSortCountsmt2hmerge
  (Tip2015treesortAddSamesmt2Node z227 x2104 x368)
  (Tip2015treesortAddSamesmt2Node x447 x518 x617) =
  case x2104 P.<= x518 of
    P.True ->
      Tip2015treesortAddSamesmt2Node
        (tip2015sortHSortCountsmt2hmerge
           x368 (Tip2015treesortAddSamesmt2Node x447 x518 x617))
        x2104 z227
    P.False ->
      Tip2015treesortAddSamesmt2Node
        (tip2015sortHSortCountsmt2hmerge
           (Tip2015treesortAddSamesmt2Node z227 x2104 x368) x617)
        x518 x447
tip2015sortHSortCountsmt2hmerge
  (Tip2015treesortAddSamesmt2Node z227 x2104 x368)
  Tip2015treesortAddSamesmt2Nil =
  Tip2015treesortAddSamesmt2Node z227 x2104 x368
tip2015sortHSortCountsmt2hmerge
  Tip2015treesortAddSamesmt2Nil y299 =
  y299
tip2015sortHSortCountsmt2hpairwise ::
  Grammarssimpexprunambig3smt2list
    (Tip2015treesortAddSamesmt2Tree P.Int) ->
    Grammarssimpexprunambig3smt2list
      (Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortHSortCountsmt2hpairwise Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortHSortCountsmt2hpairwise (Cons q21 Nil) =
  Cons
    q21
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Tip2015treesortAddSamesmt2Tree P.Int))
tip2015sortHSortCountsmt2hpairwise (Cons q21 (Cons q27 qs3)) =
  Cons
    (tip2015sortHSortCountsmt2hmerge q21 q27)
    (tip2015sortHSortCountsmt2hpairwise qs3)
tip2015sortHSortCountsmt2hmerging ::
  Grammarssimpexprunambig3smt2list
    (Tip2015treesortAddSamesmt2Tree P.Int) ->
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortHSortCountsmt2hmerging Nil =
  Tip2015treesortAddSamesmt2Nil ::
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortHSortCountsmt2hmerging (Cons q28 Nil) = q28
tip2015sortHSortCountsmt2hmerging (Cons q28 (Cons z228 x2105)) =
  tip2015sortHSortCountsmt2hmerging
    (tip2015sortHSortCountsmt2hpairwise (Cons q28 (Cons z228 x2105)))
tip2015sortHSortCountsmt2toHeap ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortHSortCountsmt2toHeap x369 =
  tip2015sortHSortCountsmt2hmerging
    (tip2015sortHSortCountsmt2toHeap2 x369)
tip2015sortHSortCountsmt2toList ::
  Tip2015treesortAddSamesmt2Tree P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortHSortCountsmt2toList
  (Tip2015treesortAddSamesmt2Node q29 y300 q210) =
  Cons
    y300
    (tip2015sortHSortCountsmt2toList
       (tip2015sortHSortCountsmt2hmerge q29 q210))
tip2015sortHSortCountsmt2toList Tip2015treesortAddSamesmt2Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortHSortCountsmt2hsort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortHSortCountsmt2hsort x370 =
  tip2015sortHSortCountsmt2toList
    (tip2015sortHSortCountsmt2toHeap x370)
tip2015sortNMSortTDSortssmt2zisaplannerprop78smt2sorted ::
  Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortNMSortTDSortssmt2zisaplannerprop78smt2sorted Nil =
  P.True
tip2015sortNMSortTDSortssmt2zisaplannerprop78smt2sorted
  (Cons y301 Nil) =
  P.True
tip2015sortNMSortTDSortssmt2zisaplannerprop78smt2sorted
  (Cons y301 (Cons y2100 xs170)) =
  (y301 P.<= y2100) P.&&
    (tip2015sortNMSortTDSortssmt2zisaplannerprop78smt2sorted
       (Cons y2100 xs170))
tip2015sortNMSortTDSortssmt2lmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortNMSortTDSortssmt2lmerge Nil y302 = y302
tip2015sortNMSortTDSortssmt2lmerge (Cons z229 x2106) Nil =
  Cons z229 x2106
tip2015sortNMSortTDSortssmt2lmerge
  (Cons z229 x2106) (Cons x371 x448) =
  case z229 P.<= x371 of
    P.True ->
      Cons
        z229 (tip2015sortNMSortTDSortssmt2lmerge x2106 (Cons x371 x448))
    P.False ->
      Cons
        x371 (tip2015sortNMSortTDSortssmt2lmerge (Cons z229 x2106) x448)
tip2015sortNMSortTDSortssmt2nmsorttd ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortNMSortTDSortssmt2nmsorttd Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortNMSortTDSortssmt2nmsorttd (Cons y303 Nil) =
  Cons y303 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortNMSortTDSortssmt2nmsorttd
  (Cons y303 (Cons x2107 x372)) =
  let k6 =
        half (isaplannerprop68smt2len (Cons y303 (Cons x2107 x372)))
    in tip2015sortNMSortTDSortssmt2lmerge
         (tip2015sortNMSortTDSortssmt2nmsorttd
            (isaplannerprop82smt2take k6 (Cons y303 (Cons x2107 x372))))
         (tip2015sortNMSortTDSortssmt2nmsorttd
            (isaplannerprop12smt2drop k6 (Cons y303 (Cons x2107 x372))))
tip2015listzcountnubsmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015listzcountnubsmt2zelem x373 Nil = P.False
tip2015listzcountnubsmt2zelem x373 (Cons z230 ys109) =
  (x373 P.== z230) P.|| (tip2015listzcountnubsmt2zelem x373 ys109)
tip2015listzcountnubsmt2zdeleteAll ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015listzcountnubsmt2zdeleteAll x374 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015listzcountnubsmt2zdeleteAll x374 (Cons z231 xs171) =
  case x374 P.== z231 of
    P.True -> tip2015listzcountnubsmt2zdeleteAll x374 xs171
    P.False ->
      Cons z231 (tip2015listzcountnubsmt2zdeleteAll x374 xs171)
tip2015listzcountnubsmt2znub ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015listzcountnubsmt2znub Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015listzcountnubsmt2znub (Cons y304 xs172) =
  Cons
    y304
    (tip2015listzcountnubsmt2zdeleteAll
       y304 (tip2015listzcountnubsmt2znub xs172))
tip2015listzcountnubsmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015listzcountnubsmt2zcount x375 Nil = Isaplannerprop54smt2Z
tip2015listzcountnubsmt2zcount x375 (Cons z232 xs173) =
  case x375 P.== z232 of
    P.True ->
      Isaplannerprop54smt2S (tip2015listzcountnubsmt2zcount x375 xs173)
    P.False -> tip2015listzcountnubsmt2zcount x375 xs173
tip2015propositionalAndIdempotentsmt2models4 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list
      (Isaplannerprop45smt2Pair P.Int P.Bool) ->
      Grammarssimpexprunambig3smt2list P.Bool
tip2015propositionalAndIdempotentsmt2models4 x376 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Bool
tip2015propositionalAndIdempotentsmt2models4
  x376 (Cons (Pair2 y2101 P.True) x2108) =
  tip2015propositionalAndIdempotentsmt2models4 x376 x2108
tip2015propositionalAndIdempotentsmt2models4
  x376 (Cons (Pair2 y2101 P.False) x2108) =
  Cons
    (x376 P.== y2101)
    (tip2015propositionalAndIdempotentsmt2models4 x376 x2108)
tip2015propositionalAndIdempotentsmt2models3 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list
      (Isaplannerprop45smt2Pair P.Int P.Bool) ->
      Grammarssimpexprunambig3smt2list P.Bool
tip2015propositionalAndIdempotentsmt2models3 x377 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Bool
tip2015propositionalAndIdempotentsmt2models3
  x377 (Cons (Pair2 y2102 P.True) x2109) =
  Cons
    (x377 P.== y2102)
    (tip2015propositionalAndIdempotentsmt2models3 x377 x2109)
tip2015propositionalAndIdempotentsmt2models3
  x377 (Cons (Pair2 y2102 P.False) x2109) =
  tip2015propositionalAndIdempotentsmt2models3 x377 x2109
tip2015polyrecseqindexsmt2pair ::
  Grammarssimpexprunambig3smt2list a97 ->
    Grammarssimpexprunambig3smt2list
      (Isaplannerprop45smt2Pair a97 (Maybe a97))
tip2015polyrecseqindexsmt2pair Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Isaplannerprop45smt2Pair a97 (Maybe a97))
tip2015polyrecseqindexsmt2pair (Cons y305 Nil) =
  Cons
    (Pair2 y305 (Nothing :: Maybe a97))
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Isaplannerprop45smt2Pair a97 (Maybe a97)))
tip2015polyrecseqindexsmt2pair (Cons y305 (Cons y2103 xs174)) =
  Cons
    (Pair2 y305 (Tip2015heapdeleteMinimumsmt2Just y2103))
    (tip2015polyrecseqindexsmt2pair xs174)
lookup ::
  P.Int -> Grammarssimpexprunambig3smt2list a98 -> Maybe a98
lookup x378 Nil = Nothing :: Maybe a98
lookup x378 (Cons z233 x2110) =
  case x378 P.== (0) of
    P.True -> Tip2015heapdeleteMinimumsmt2Just z233
    P.False -> lookup (x378 P.- (1)) x2110
fromList ::
  Grammarssimpexprunambig3smt2list a99 ->
    Tip2015polyrecseqindexsmt2Seq a99
fromList Nil =
  Tip2015polyrecseqindexsmt2Nil :: Tip2015polyrecseqindexsmt2Seq a99
fromList (Cons y306 xs175) =
  Tip2015polyrecseqindexsmt2Cons
    y306 (fromList (tip2015polyrecseqindexsmt2pair xs175))
tip2015sortBSortPermutessmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortBSortPermutessmt2zelem x379 Nil = P.False
tip2015sortBSortPermutessmt2zelem x379 (Cons z234 ys110) =
  (x379 P.== z234) P.||
    (tip2015sortBSortPermutessmt2zelem x379 ys110)
tip2015sortBSortPermutessmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortPermutessmt2zdelete x380 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortPermutessmt2zdelete x380 (Cons z235 ys111) =
  case x380 P.== z235 of
    P.True -> ys111
    P.False ->
      Cons z235 (tip2015sortBSortPermutessmt2zdelete x380 ys111)
tip2015sortBSortPermutessmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortPermutessmt2sort2 x381 y307 =
  case x381 P.<= y307 of
    P.True ->
      Cons
        x381 (Cons y307 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y307 (Cons x381 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortBSortPermutessmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortBSortPermutessmt2zisPermutation Nil y308 = null y308
tip2015sortBSortPermutessmt2zisPermutation (Cons z236 xs176) y308 =
  (tip2015sortBSortPermutessmt2zelem z236 y308) P.&&
    (tip2015sortBSortPermutessmt2zisPermutation
       xs176 (tip2015sortBSortPermutessmt2zdelete z236 y308))
tip2015sortBSortPermutessmt2evens ::
  Grammarssimpexprunambig3smt2list a100 ->
    Grammarssimpexprunambig3smt2list a100
tip2015sortBSortPermutessmt2evens Nil =
  Nil :: Grammarssimpexprunambig3smt2list a100
tip2015sortBSortPermutessmt2evens (Cons y309 xs177) =
  Cons y309 (tip2015sortBSortPermutessmt2odds xs177)
tip2015sortBSortPermutessmt2odds ::
  Grammarssimpexprunambig3smt2list a101 ->
    Grammarssimpexprunambig3smt2list a101
tip2015sortBSortPermutessmt2odds Nil =
  Nil :: Grammarssimpexprunambig3smt2list a101
tip2015sortBSortPermutessmt2odds (Cons y312 xs178) =
  tip2015sortBSortPermutessmt2evens xs178
tip2015sortBSortPermutessmt2pairs ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortPermutessmt2pairs Nil y313 = y313
tip2015sortBSortPermutessmt2pairs (Cons z237 x2111) Nil =
  Cons z237 x2111
tip2015sortBSortPermutessmt2pairs
  (Cons z237 x2111) (Cons x382 x449) =
  append
    (tip2015sortBSortPermutessmt2sort2 z237 x382)
    (tip2015sortBSortPermutessmt2pairs x2111 x449)
tip2015sortBSortPermutessmt2stitch ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortPermutessmt2stitch Nil y314 = y314
tip2015sortBSortPermutessmt2stitch (Cons z238 xs179) y314 =
  Cons z238 (tip2015sortBSortPermutessmt2pairs xs179 y314)
tip2015sortBSortPermutessmt2bmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortPermutessmt2bmerge Nil y315 =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortPermutessmt2bmerge (Cons z239 x2112) Nil =
  Cons z239 x2112
tip2015sortBSortPermutessmt2bmerge
  (Cons z239 Nil) (Cons x383 Nil) =
  tip2015sortBSortPermutessmt2sort2 z239 x383
tip2015sortBSortPermutessmt2bmerge
  (Cons z239 Nil) (Cons x383 (Cons x519 x618)) =
  tip2015sortBSortPermutessmt2stitch
    (tip2015sortBSortPermutessmt2bmerge
       (tip2015sortBSortPermutessmt2evens
          (Cons z239 (Nil :: Grammarssimpexprunambig3smt2list P.Int)))
       (tip2015sortBSortPermutessmt2evens (Cons x383 (Cons x519 x618))))
    (tip2015sortBSortPermutessmt2bmerge
       (tip2015sortBSortPermutessmt2odds
          (Cons z239 (Nil :: Grammarssimpexprunambig3smt2list P.Int)))
       (tip2015sortBSortPermutessmt2odds (Cons x383 (Cons x519 x618))))
tip2015sortBSortPermutessmt2bmerge
  (Cons z239 (Cons x712 x812)) (Cons x383 x450) =
  tip2015sortBSortPermutessmt2stitch
    (tip2015sortBSortPermutessmt2bmerge
       (tip2015sortBSortPermutessmt2evens (Cons z239 (Cons x712 x812)))
       (tip2015sortBSortPermutessmt2evens (Cons x383 x450)))
    (tip2015sortBSortPermutessmt2bmerge
       (tip2015sortBSortPermutessmt2odds (Cons z239 (Cons x712 x812)))
       (tip2015sortBSortPermutessmt2odds (Cons x383 x450)))
tip2015sortBSortPermutessmt2bsort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortPermutessmt2bsort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortPermutessmt2bsort (Cons y316 Nil) =
  Cons y316 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortBSortPermutessmt2bsort (Cons y316 (Cons x2113 x384)) =
  tip2015sortBSortPermutessmt2bmerge
    (tip2015sortBSortPermutessmt2bsort
       (tip2015sortBSortPermutessmt2evens (Cons y316 (Cons x2113 x384))))
    (tip2015sortBSortPermutessmt2bsort
       (tip2015sortBSortPermutessmt2odds (Cons y316 (Cons x2113 x384))))
tip2015listzelemnublsmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015listzelemnublsmt2zelem x385 Nil = P.False
tip2015listzelemnublsmt2zelem x385 (Cons z240 ys112) =
  (x385 P.== z240) P.|| (tip2015listzelemnublsmt2zelem x385 ys112)
tip2015listzelemnublsmt2zdeleteAll ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015listzelemnublsmt2zdeleteAll x386 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015listzelemnublsmt2zdeleteAll x386 (Cons z241 xs180) =
  case x386 P.== z241 of
    P.True -> tip2015listzelemnublsmt2zdeleteAll x386 xs180
    P.False ->
      Cons z241 (tip2015listzelemnublsmt2zdeleteAll x386 xs180)
tip2015listzelemnublsmt2znub ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015listzelemnublsmt2znub Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015listzelemnublsmt2znub (Cons y317 xs181) =
  Cons
    y317
    (tip2015listzelemnublsmt2zdeleteAll
       y317 (tip2015listzelemnublsmt2znub xs181))
eqList ::
  Grammarssimpexprunambig3smt2list Grammarssimpexprunambig5smt2T ->
    Grammarssimpexprunambig3smt2list Grammarssimpexprunambig5smt2T ->
      P.Bool
eqList Nil Nil = P.True
eqList Nil (Cons z242 x2114) = P.False
eqList (Cons x387 xs182) Nil = P.False
eqList (Cons x387 xs182) (Cons y2104 ys113) =
  (eqA x387 y2104) P.&& (eqList xs182 ys113)
tip2015propositionalAndImplicationsmt2models4 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list
      (Isaplannerprop45smt2Pair P.Int P.Bool) ->
      Grammarssimpexprunambig3smt2list P.Bool
tip2015propositionalAndImplicationsmt2models4 x388 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Bool
tip2015propositionalAndImplicationsmt2models4
  x388 (Cons (Pair2 y2105 P.True) x2115) =
  tip2015propositionalAndImplicationsmt2models4 x388 x2115
tip2015propositionalAndImplicationsmt2models4
  x388 (Cons (Pair2 y2105 P.False) x2115) =
  Cons
    (x388 P.== y2105)
    (tip2015propositionalAndImplicationsmt2models4 x388 x2115)
tip2015propositionalAndImplicationsmt2models3 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list
      (Isaplannerprop45smt2Pair P.Int P.Bool) ->
      Grammarssimpexprunambig3smt2list P.Bool
tip2015propositionalAndImplicationsmt2models3 x389 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Bool
tip2015propositionalAndImplicationsmt2models3
  x389 (Cons (Pair2 y2106 P.True) x2116) =
  Cons
    (x389 P.== y2106)
    (tip2015propositionalAndImplicationsmt2models3 x389 x2116)
tip2015propositionalAndImplicationsmt2models3
  x389 (Cons (Pair2 y2106 P.False) x2116) =
  tip2015propositionalAndImplicationsmt2models3 x389 x2116
tip2015sortTSortCountsmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015sortTSortCountsmt2zcount x390 Nil = Isaplannerprop54smt2Z
tip2015sortTSortCountsmt2zcount x390 (Cons z243 xs183) =
  case x390 P.== z243 of
    P.True ->
      Isaplannerprop54smt2S (tip2015sortTSortCountsmt2zcount x390 xs183)
    P.False -> tip2015sortTSortCountsmt2zcount x390 xs183
tip2015sortTSortCountsmt2add ::
  P.Int ->
    Tip2015treesortAddSamesmt2Tree P.Int ->
      Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortTSortCountsmt2add
  x391 (Tip2015treesortAddSamesmt2Node q30 z244 q211) =
  case x391 P.<= z244 of
    P.True ->
      Tip2015treesortAddSamesmt2Node
        (tip2015sortTSortCountsmt2add x391 q30) z244 q211
    P.False ->
      Tip2015treesortAddSamesmt2Node
        q30 z244 (tip2015sortTSortCountsmt2add x391 q211)
tip2015sortTSortCountsmt2add x391 Tip2015treesortAddSamesmt2Nil =
  Tip2015treesortAddSamesmt2Node
    (Tip2015treesortAddSamesmt2Nil ::
       Tip2015treesortAddSamesmt2Tree P.Int)
    x391
    (Tip2015treesortAddSamesmt2Nil ::
       Tip2015treesortAddSamesmt2Tree P.Int)
tip2015sortTSortCountsmt2toTree ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortTSortCountsmt2toTree Nil =
  Tip2015treesortAddSamesmt2Nil ::
    Tip2015treesortAddSamesmt2Tree P.Int
tip2015sortTSortCountsmt2toTree (Cons y318 xs184) =
  tip2015sortTSortCountsmt2add
    y318 (tip2015sortTSortCountsmt2toTree xs184)
tip2015sortTSortCountsmt2tsort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortTSortCountsmt2tsort x392 =
  tip2015treesortAddSamesmt2flatten
    (tip2015sortTSortCountsmt2toTree x392)
    (Nil :: Grammarssimpexprunambig3smt2list P.Int)
interleave ::
  Grammarssimpexprunambig3smt2list a102 ->
    Grammarssimpexprunambig3smt2list a102 ->
      Grammarssimpexprunambig3smt2list a102
interleave Nil y319 = y319
interleave (Cons z245 xs185) y319 =
  Cons z245 (interleave y319 xs185)
tip2015listInterleavesmt2evens ::
  Grammarssimpexprunambig3smt2list a103 ->
    Grammarssimpexprunambig3smt2list a103
tip2015listInterleavesmt2evens Nil =
  Nil :: Grammarssimpexprunambig3smt2list a103
tip2015listInterleavesmt2evens (Cons y320 xs186) =
  Cons y320 (tip2015listInterleavesmt2odds xs186)
tip2015listInterleavesmt2odds ::
  Grammarssimpexprunambig3smt2list a104 ->
    Grammarssimpexprunambig3smt2list a104
tip2015listInterleavesmt2odds Nil =
  Nil :: Grammarssimpexprunambig3smt2list a104
tip2015listInterleavesmt2odds (Cons y321 xs187) =
  tip2015listInterleavesmt2evens xs187
tip2015sortBSortSortssmt2zisaplannerprop78smt2sorted ::
  Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortBSortSortssmt2zisaplannerprop78smt2sorted Nil = P.True
tip2015sortBSortSortssmt2zisaplannerprop78smt2sorted
  (Cons y322 Nil) =
  P.True
tip2015sortBSortSortssmt2zisaplannerprop78smt2sorted
  (Cons y322 (Cons y2107 xs188)) =
  (y322 P.<= y2107) P.&&
    (tip2015sortBSortSortssmt2zisaplannerprop78smt2sorted
       (Cons y2107 xs188))
tip2015sortBSortSortssmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortSortssmt2sort2 x393 y323 =
  case x393 P.<= y323 of
    P.True ->
      Cons
        x393 (Cons y323 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y323 (Cons x393 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortBSortSortssmt2evens ::
  Grammarssimpexprunambig3smt2list a105 ->
    Grammarssimpexprunambig3smt2list a105
tip2015sortBSortSortssmt2evens Nil =
  Nil :: Grammarssimpexprunambig3smt2list a105
tip2015sortBSortSortssmt2evens (Cons y324 xs189) =
  Cons y324 (tip2015sortBSortSortssmt2odds xs189)
tip2015sortBSortSortssmt2odds ::
  Grammarssimpexprunambig3smt2list a106 ->
    Grammarssimpexprunambig3smt2list a106
tip2015sortBSortSortssmt2odds Nil =
  Nil :: Grammarssimpexprunambig3smt2list a106
tip2015sortBSortSortssmt2odds (Cons y325 xs190) =
  tip2015sortBSortSortssmt2evens xs190
tip2015sortBSortSortssmt2pairs ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortSortssmt2pairs Nil y326 = y326
tip2015sortBSortSortssmt2pairs (Cons z246 x2117) Nil =
  Cons z246 x2117
tip2015sortBSortSortssmt2pairs (Cons z246 x2117) (Cons x394 x451) =
  append
    (tip2015sortBSortSortssmt2sort2 z246 x394)
    (tip2015sortBSortSortssmt2pairs x2117 x451)
tip2015sortBSortSortssmt2stitch ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortSortssmt2stitch Nil y327 = y327
tip2015sortBSortSortssmt2stitch (Cons z247 xs191) y327 =
  Cons z247 (tip2015sortBSortSortssmt2pairs xs191 y327)
tip2015sortBSortSortssmt2bmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortSortssmt2bmerge Nil y328 =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortSortssmt2bmerge (Cons z248 x2118) Nil =
  Cons z248 x2118
tip2015sortBSortSortssmt2bmerge (Cons z248 Nil) (Cons x395 Nil) =
  tip2015sortBSortSortssmt2sort2 z248 x395
tip2015sortBSortSortssmt2bmerge
  (Cons z248 Nil) (Cons x395 (Cons x520 x619)) =
  tip2015sortBSortSortssmt2stitch
    (tip2015sortBSortSortssmt2bmerge
       (tip2015sortBSortSortssmt2evens
          (Cons z248 (Nil :: Grammarssimpexprunambig3smt2list P.Int)))
       (tip2015sortBSortSortssmt2evens (Cons x395 (Cons x520 x619))))
    (tip2015sortBSortSortssmt2bmerge
       (tip2015sortBSortSortssmt2odds
          (Cons z248 (Nil :: Grammarssimpexprunambig3smt2list P.Int)))
       (tip2015sortBSortSortssmt2odds (Cons x395 (Cons x520 x619))))
tip2015sortBSortSortssmt2bmerge
  (Cons z248 (Cons x713 x813)) (Cons x395 x452) =
  tip2015sortBSortSortssmt2stitch
    (tip2015sortBSortSortssmt2bmerge
       (tip2015sortBSortSortssmt2evens (Cons z248 (Cons x713 x813)))
       (tip2015sortBSortSortssmt2evens (Cons x395 x452)))
    (tip2015sortBSortSortssmt2bmerge
       (tip2015sortBSortSortssmt2odds (Cons z248 (Cons x713 x813)))
       (tip2015sortBSortSortssmt2odds (Cons x395 x452)))
tip2015sortBSortSortssmt2bsort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortSortssmt2bsort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortBSortSortssmt2bsort (Cons y329 Nil) =
  Cons y329 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortBSortSortssmt2bsort (Cons y329 (Cons x2119 x396)) =
  tip2015sortBSortSortssmt2bmerge
    (tip2015sortBSortSortssmt2bsort
       (tip2015sortBSortSortssmt2evens (Cons y329 (Cons x2119 x396))))
    (tip2015sortBSortSortssmt2bsort
       (tip2015sortBSortSortssmt2odds (Cons y329 (Cons x2119 x396))))
tip2015sortMSortBU2Countsmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015sortMSortBU2Countsmt2zcount x397 Nil = Isaplannerprop54smt2Z
tip2015sortMSortBU2Countsmt2zcount x397 (Cons z249 xs192) =
  case x397 P.== z249 of
    P.True ->
      Isaplannerprop54smt2S
        (tip2015sortMSortBU2Countsmt2zcount x397 xs192)
    P.False -> tip2015sortMSortBU2Countsmt2zcount x397 xs192
tip2015sortMSortBU2Countsmt2risers ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBU2Countsmt2risers Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBU2Countsmt2risers (Cons y330 Nil) =
  Cons
    (Cons y330 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Grammarssimpexprunambig3smt2list P.Int))
tip2015sortMSortBU2Countsmt2risers (Cons y330 (Cons y2108 xs193)) =
  case y330 P.<= y2108 of
    P.True ->
      case tip2015sortMSortBU2Countsmt2risers (Cons y2108 xs193) of
        Nil ->
          Nil ::
            Grammarssimpexprunambig3smt2list
              (Grammarssimpexprunambig3smt2list P.Int)
        Cons ys114 yss4 -> Cons (Cons y330 ys114) yss4
    P.False ->
      Cons
        (Cons y330 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
        (tip2015sortMSortBU2Countsmt2risers (Cons y2108 xs193))
tip2015sortMSortBU2Countsmt2lmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2Countsmt2lmerge Nil y331 = y331
tip2015sortMSortBU2Countsmt2lmerge (Cons z250 x2120) Nil =
  Cons z250 x2120
tip2015sortMSortBU2Countsmt2lmerge
  (Cons z250 x2120) (Cons x398 x453) =
  case z250 P.<= x398 of
    P.True ->
      Cons
        z250 (tip2015sortMSortBU2Countsmt2lmerge x2120 (Cons x398 x453))
    P.False ->
      Cons
        x398 (tip2015sortMSortBU2Countsmt2lmerge (Cons z250 x2120) x453)
tip2015sortMSortBU2Countsmt2pairwise ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list P.Int) ->
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBU2Countsmt2pairwise Nil =
  Nil ::
    Grammarssimpexprunambig3smt2list
      (Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortBU2Countsmt2pairwise (Cons xs194 Nil) =
  Cons
    xs194
    (Nil ::
       Grammarssimpexprunambig3smt2list
         (Grammarssimpexprunambig3smt2list P.Int))
tip2015sortMSortBU2Countsmt2pairwise
  (Cons xs194 (Cons ys115 xss9)) =
  Cons
    (tip2015sortMSortBU2Countsmt2lmerge xs194 ys115)
    (tip2015sortMSortBU2Countsmt2pairwise xss9)
tip2015sortMSortBU2Countsmt2mergingbu2 ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list P.Int) ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2Countsmt2mergingbu2 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2Countsmt2mergingbu2 (Cons xs195 Nil) = xs195
tip2015sortMSortBU2Countsmt2mergingbu2
  (Cons xs195 (Cons z251 x2121)) =
  tip2015sortMSortBU2Countsmt2mergingbu2
    (tip2015sortMSortBU2Countsmt2pairwise
       (Cons xs195 (Cons z251 x2121)))
tip2015sortMSortBU2Countsmt2msortbu2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortBU2Countsmt2msortbu2 x399 =
  tip2015sortMSortBU2Countsmt2mergingbu2
    (tip2015sortMSortBU2Countsmt2risers x399)
tip2015sortISortPermutessmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortISortPermutessmt2zelem x400 Nil = P.False
tip2015sortISortPermutessmt2zelem x400 (Cons z252 ys116) =
  (x400 P.== z252) P.||
    (tip2015sortISortPermutessmt2zelem x400 ys116)
tip2015sortISortPermutessmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortISortPermutessmt2zdelete x401 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortISortPermutessmt2zdelete x401 (Cons z253 ys117) =
  case x401 P.== z253 of
    P.True -> ys117
    P.False ->
      Cons z253 (tip2015sortISortPermutessmt2zdelete x401 ys117)
tip2015sortISortPermutessmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortISortPermutessmt2zisPermutation Nil y332 = null y332
tip2015sortISortPermutessmt2zisPermutation (Cons z254 xs196) y332 =
  (tip2015sortISortPermutessmt2zelem z254 y332) P.&&
    (tip2015sortISortPermutessmt2zisPermutation
       xs196 (tip2015sortISortPermutessmt2zdelete z254 y332))
tip2015sortISortPermutessmt2insert2 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortISortPermutessmt2insert2 x402 Nil =
  Cons x402 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortISortPermutessmt2insert2 x402 (Cons z255 xs197) =
  case x402 P.<= z255 of
    P.True -> Cons x402 (Cons z255 xs197)
    P.False ->
      Cons z255 (tip2015sortISortPermutessmt2insert2 x402 xs197)
tip2015sortISortPermutessmt2isort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortISortPermutessmt2isort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortISortPermutessmt2isort (Cons y333 xs198) =
  tip2015sortISortPermutessmt2insert2
    y333 (tip2015sortISortPermutessmt2isort xs198)
tip2015sortMSortTDCountsmt2ztake ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a107 ->
      Grammarssimpexprunambig3smt2list a107
tip2015sortMSortTDCountsmt2ztake x403 y334 =
  case x403 P.== (0) of
    P.True -> Nil :: Grammarssimpexprunambig3smt2list a107
    P.False ->
      case y334 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a107
        Cons z256 xs199 ->
          Cons z256 (tip2015sortMSortTDCountsmt2ztake (x403 P.- (1)) xs199)
tip2015sortMSortTDCountsmt2zlength ::
  Grammarssimpexprunambig3smt2list a108 -> P.Int
tip2015sortMSortTDCountsmt2zlength Nil = 0
tip2015sortMSortTDCountsmt2zlength (Cons y335 xs200) =
  (1) P.+ (tip2015sortMSortTDCountsmt2zlength xs200)
tip2015sortMSortTDCountsmt2zdrop ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a109 ->
      Grammarssimpexprunambig3smt2list a109
tip2015sortMSortTDCountsmt2zdrop x404 y336 =
  case x404 P.== (0) of
    P.True -> y336
    P.False ->
      case y336 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a109
        Cons z257 xs1100 ->
          tip2015sortMSortTDCountsmt2zdrop (x404 P.- (1)) xs1100
tip2015sortMSortTDCountsmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015sortMSortTDCountsmt2zcount x405 Nil = Isaplannerprop54smt2Z
tip2015sortMSortTDCountsmt2zcount x405 (Cons z258 xs201) =
  case x405 P.== z258 of
    P.True ->
      Isaplannerprop54smt2S
        (tip2015sortMSortTDCountsmt2zcount x405 xs201)
    P.False -> tip2015sortMSortTDCountsmt2zcount x405 xs201
tip2015sortMSortTDCountsmt2lmerge ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortTDCountsmt2lmerge Nil y337 = y337
tip2015sortMSortTDCountsmt2lmerge (Cons z259 x2122) Nil =
  Cons z259 x2122
tip2015sortMSortTDCountsmt2lmerge
  (Cons z259 x2122) (Cons x3100 x454) =
  case z259 P.<= x3100 of
    P.True ->
      Cons
        z259 (tip2015sortMSortTDCountsmt2lmerge x2122 (Cons x3100 x454))
    P.False ->
      Cons
        x3100 (tip2015sortMSortTDCountsmt2lmerge (Cons z259 x2122) x454)
tip2015sortMSortTDCountsmt2msorttd ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortTDCountsmt2msorttd Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortMSortTDCountsmt2msorttd (Cons y338 Nil) =
  Cons y338 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortMSortTDCountsmt2msorttd (Cons y338 (Cons x2123 x3101)) =
  let k7 =
        P.div
          (tip2015sortMSortTDCountsmt2zlength (Cons y338 (Cons x2123 x3101)))
          (2)
    in tip2015sortMSortTDCountsmt2lmerge
         (tip2015sortMSortTDCountsmt2msorttd
            (tip2015sortMSortTDCountsmt2ztake
               k7 (Cons y338 (Cons x2123 x3101))))
         (tip2015sortMSortTDCountsmt2msorttd
            (tip2015sortMSortTDCountsmt2zdrop
               k7 (Cons y338 (Cons x2123 x3101))))
tip2015sortQSortIsSortsmt2insert2 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortQSortIsSortsmt2insert2 x406 Nil =
  Cons x406 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortQSortIsSortsmt2insert2 x406 (Cons z260 xs202) =
  case x406 P.<= z260 of
    P.True -> Cons x406 (Cons z260 xs202)
    P.False -> Cons z260 (tip2015sortQSortIsSortsmt2insert2 x406 xs202)
tip2015sortQSortIsSortsmt2isort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortQSortIsSortsmt2isort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortQSortIsSortsmt2isort (Cons y339 xs203) =
  tip2015sortQSortIsSortsmt2insert2
    y339 (tip2015sortQSortIsSortsmt2isort xs203)
tip2015listPairEvenssmt2evens ::
  Grammarssimpexprunambig3smt2list a110 ->
    Grammarssimpexprunambig3smt2list a110
tip2015listPairEvenssmt2evens Nil =
  Nil :: Grammarssimpexprunambig3smt2list a110
tip2015listPairEvenssmt2evens (Cons y340 xs204) =
  Cons y340 (tip2015listPairEvenssmt2odds xs204)
tip2015listPairEvenssmt2odds ::
  Grammarssimpexprunambig3smt2list a111 ->
    Grammarssimpexprunambig3smt2list a111
tip2015listPairEvenssmt2odds Nil =
  Nil :: Grammarssimpexprunambig3smt2list a111
tip2015listPairEvenssmt2odds (Cons y341 xs205) =
  tip2015listPairEvenssmt2evens xs205
tip2015sortISortCountsmt2zcount ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> Isaplannerprop54smt2Nat
tip2015sortISortCountsmt2zcount x407 Nil = Isaplannerprop54smt2Z
tip2015sortISortCountsmt2zcount x407 (Cons z261 xs206) =
  case x407 P.== z261 of
    P.True ->
      Isaplannerprop54smt2S (tip2015sortISortCountsmt2zcount x407 xs206)
    P.False -> tip2015sortISortCountsmt2zcount x407 xs206
tip2015sortISortCountsmt2insert2 ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortISortCountsmt2insert2 x408 Nil =
  Cons x408 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortISortCountsmt2insert2 x408 (Cons z262 xs207) =
  case x408 P.<= z262 of
    P.True -> Cons x408 (Cons z262 xs207)
    P.False -> Cons z262 (tip2015sortISortCountsmt2insert2 x408 xs207)
tip2015sortISortCountsmt2isort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortISortCountsmt2isort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortISortCountsmt2isort (Cons y342 xs208) =
  tip2015sortISortCountsmt2insert2
    y342 (tip2015sortISortCountsmt2isort xs208)
tip2015sortStoogeSortPermutessmt2ztake ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a112 ->
      Grammarssimpexprunambig3smt2list a112
tip2015sortStoogeSortPermutessmt2ztake x409 y343 =
  case x409 P.== (0) of
    P.True -> Nil :: Grammarssimpexprunambig3smt2list a112
    P.False ->
      case y343 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a112
        Cons z263 xs209 ->
          Cons
            z263 (tip2015sortStoogeSortPermutessmt2ztake (x409 P.- (1)) xs209)
tip2015sortStoogeSortPermutessmt2zlength ::
  Grammarssimpexprunambig3smt2list a113 -> P.Int
tip2015sortStoogeSortPermutessmt2zlength Nil = 0
tip2015sortStoogeSortPermutessmt2zlength (Cons y344 xs210) =
  (1) P.+ (tip2015sortStoogeSortPermutessmt2zlength xs210)
tip2015sortStoogeSortPermutessmt2zelem ::
  P.Int -> Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortStoogeSortPermutessmt2zelem x455 Nil = P.False
tip2015sortStoogeSortPermutessmt2zelem x455 (Cons z264 ys118) =
  (x455 P.== z264) P.||
    (tip2015sortStoogeSortPermutessmt2zelem x455 ys118)
tip2015sortStoogeSortPermutessmt2zdrop ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a114 ->
      Grammarssimpexprunambig3smt2list a114
tip2015sortStoogeSortPermutessmt2zdrop x456 y345 =
  case x456 P.== (0) of
    P.True -> y345
    P.False ->
      case y345 of
        Nil -> Nil :: Grammarssimpexprunambig3smt2list a114
        Cons z265 xs1101 ->
          tip2015sortStoogeSortPermutessmt2zdrop (x456 P.- (1)) xs1101
tip2015sortStoogeSortPermutessmt2zsplitAt ::
  P.Int ->
    Grammarssimpexprunambig3smt2list a115 ->
      Isaplannerprop45smt2Pair
        (Grammarssimpexprunambig3smt2list a115)
        (Grammarssimpexprunambig3smt2list a115)
tip2015sortStoogeSortPermutessmt2zsplitAt x457 y346 =
  Pair2
    (tip2015sortStoogeSortPermutessmt2ztake x457 y346)
    (tip2015sortStoogeSortPermutessmt2zdrop x457 y346)
tip2015sortStoogeSortPermutessmt2zdelete ::
  P.Int ->
    Grammarssimpexprunambig3smt2list P.Int ->
      Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortPermutessmt2zdelete x458 Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortPermutessmt2zdelete x458 (Cons z266 ys119) =
  case x458 P.== z266 of
    P.True -> ys119
    P.False ->
      Cons z266 (tip2015sortStoogeSortPermutessmt2zdelete x458 ys119)
tip2015sortStoogeSortPermutessmt2sort2 ::
  P.Int -> P.Int -> Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortPermutessmt2sort2 x459 y347 =
  case x459 P.<= y347 of
    P.True ->
      Cons
        x459 (Cons y347 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
    P.False ->
      Cons
        y347 (Cons x459 (Nil :: Grammarssimpexprunambig3smt2list P.Int))
tip2015sortStoogeSortPermutessmt2zisPermutation ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int -> P.Bool
tip2015sortStoogeSortPermutessmt2zisPermutation Nil y348 =
  null y348
tip2015sortStoogeSortPermutessmt2zisPermutation
  (Cons z267 xs211) y348 =
  (tip2015sortStoogeSortPermutessmt2zelem z267 y348) P.&&
    (tip2015sortStoogeSortPermutessmt2zisPermutation
       xs211 (tip2015sortStoogeSortPermutessmt2zdelete z267 y348))
tip2015sortStoogeSortPermutessmt2stooge1sort2 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortPermutessmt2stooge1sort2 x460 =
  case tip2015sortStoogeSortPermutessmt2zsplitAt
         (P.div (tip2015sortStoogeSortPermutessmt2zlength x460) (3))
         (isaplannerprop85smt2rev x460) of
    Pair2 ys120 zs29 ->
      append
        (tip2015sortStoogeSortPermutessmt2stoogesort zs29)
        (isaplannerprop85smt2rev ys120)
tip2015sortStoogeSortPermutessmt2stoogesort ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortPermutessmt2stoogesort Nil =
  Nil :: Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortPermutessmt2stoogesort (Cons y349 Nil) =
  Cons y349 (Nil :: Grammarssimpexprunambig3smt2list P.Int)
tip2015sortStoogeSortPermutessmt2stoogesort
  (Cons y349 (Cons y2109 Nil)) =
  tip2015sortStoogeSortPermutessmt2sort2 y349 y2109
tip2015sortStoogeSortPermutessmt2stoogesort
  (Cons y349 (Cons y2109 (Cons x3102 x461))) =
  tip2015sortStoogeSortPermutessmt2stooge1sort2
    (tip2015sortStoogeSortPermutessmt2stooge1sort1
       (tip2015sortStoogeSortPermutessmt2stooge1sort2
          (Cons y349 (Cons y2109 (Cons x3102 x461)))))
tip2015sortStoogeSortPermutessmt2stooge1sort1 ::
  Grammarssimpexprunambig3smt2list P.Int ->
    Grammarssimpexprunambig3smt2list P.Int
tip2015sortStoogeSortPermutessmt2stooge1sort1 x462 =
  case tip2015sortStoogeSortPermutessmt2zsplitAt
         (P.div (tip2015sortStoogeSortPermutessmt2zlength x462) (3)) x462 of
    Pair2 ys121 zs30 ->
      append ys121 (tip2015sortStoogeSortPermutessmt2stoogesort zs30)
tip2015heapminimumsmt2minimum ::
  Tip2015heapSortPermutessmt2Heap -> Maybe Isaplannerprop54smt2Nat
tip2015heapminimumsmt2minimum
  (Tip2015heapSortPermutessmt2Node y350 z268 x2124) =
  Tip2015heapdeleteMinimumsmt2Just z268
tip2015heapminimumsmt2minimum Tip2015heapSortPermutessmt2Nil =
  Nothing :: Maybe Isaplannerprop54smt2Nat
listMinimum ::
  Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
    Maybe Isaplannerprop54smt2Nat
listMinimum Nil = Nothing :: Maybe Isaplannerprop54smt2Nat
listMinimum (Cons y351 z269) =
  Tip2015heapdeleteMinimumsmt2Just y351
prodprop12smt2qrev ::
  Grammarssimpexprunambig3smt2list a116 ->
    Grammarssimpexprunambig3smt2list a116 ->
      Grammarssimpexprunambig3smt2list a116
prodprop12smt2qrev Nil y352 = y352
prodprop12smt2qrev (Cons z270 xs212) y352 =
  prodprop12smt2qrev xs212 (Cons z270 y352)
qexp ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat ->
      Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
qexp x463 Isaplannerprop54smt2Z z271 = z271
qexp x463 (Isaplannerprop54smt2S n13) z271 =
  qexp x463 n13 (tip2015nataltmulsamesmt2mult x463 z271)
prodprop35smt2exp ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
prodprop35smt2exp x464 Isaplannerprop54smt2Z =
  Isaplannerprop54smt2S Isaplannerprop54smt2Z
prodprop35smt2exp x464 (Isaplannerprop54smt2S n14) =
  tip2015nataltmulsamesmt2mult x464 (prodprop35smt2exp x464 n14)
subset2 ::
  Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat -> P.Bool
subset2 Nil y353 = P.True
subset2 (Cons z272 xs213) y353 =
  (isaplannerprop37smt2elem z272 y353) P.&& (subset2 xs213 y353)
union2 ::
  Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
      Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
union2 Nil y354 = y354
union2 (Cons z273 xs214) y354 =
  case isaplannerprop37smt2elem z273 y354 of
    P.True -> union2 xs214 y354
    P.False -> Cons z273 (union2 xs214 y354)
intersect2 ::
  Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
    Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat ->
      Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
intersect2 Nil y355 =
  Nil :: Grammarssimpexprunambig3smt2list Isaplannerprop54smt2Nat
intersect2 (Cons z274 xs215) y355 =
  case isaplannerprop37smt2elem z274 y355 of
    P.True -> Cons z274 (intersect2 xs215 y355)
    P.False -> intersect2 xs215 y355
double :: Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
double Isaplannerprop54smt2Z = Isaplannerprop54smt2Z
double (Isaplannerprop54smt2S y356) =
  Isaplannerprop54smt2S (Isaplannerprop54smt2S (double y356))
qfac ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
qfac Isaplannerprop54smt2Z y357 = y357
qfac (Isaplannerprop54smt2S z275) y357 =
  qfac
    z275
    (tip2015nataltmulsamesmt2mult (Isaplannerprop54smt2S z275) y357)
qrevflat ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list a117) ->
    Grammarssimpexprunambig3smt2list a117 ->
      Grammarssimpexprunambig3smt2list a117
qrevflat Nil y358 = y358
qrevflat (Cons xs216 xss10) y358 =
  qrevflat xss10 (append (isaplannerprop85smt2rev xs216) y358)
prodprop28smt2revflat ::
  Grammarssimpexprunambig3smt2list
    (Grammarssimpexprunambig3smt2list a118) ->
    Grammarssimpexprunambig3smt2list a118
prodprop28smt2revflat Nil =
  Nil :: Grammarssimpexprunambig3smt2list a118
prodprop28smt2revflat (Cons xs217 xss11) =
  append
    (prodprop28smt2revflat xss11) (isaplannerprop85smt2rev xs217)
mult2 ::
  Isaplannerprop54smt2Nat ->
    Isaplannerprop54smt2Nat ->
      Isaplannerprop54smt2Nat -> Isaplannerprop54smt2Nat
mult2 Isaplannerprop54smt2Z y359 z276 = z276
mult2 (Isaplannerprop54smt2S x2125) y359 z276 =
  mult2 x2125 y359 (isaplannerprop54smt2plus y359 z276)
