{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
module A where
import qualified Text.Show.Functions
import qualified Data.Typeable as T
import qualified Prelude as P
import qualified GHC.Generics
import qualified Data.Serialize
import qualified Test.Feat as F
import qualified Test.QuickCheck as QC
data List locala = Nil | Cons locala (List locala)
  deriving (GHC.Generics.Generic, P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''List)
instance (Data.Serialize.Serialize a) => Data.Serialize.Serialize (List a)
instance (F.Enumerable locala) => QC.Arbitrary (List locala) where
  arbitrary = QC.sized F.uniform
data Nat = Z | Prodprop14smt2S Nat
  deriving (GHC.Generics.Generic, P.Eq, P.Ord, P.Show, T.Typeable)
F.deriveEnumerable (''Nat)
instance Data.Serialize.Serialize Nat
instance QC.Arbitrary Nat where arbitrary = QC.sized F.uniform
le :: Nat -> Nat -> P.Bool
le Z localy = P.True
le (Prodprop14smt2S localz) Z = P.False
le (Prodprop14smt2S localz) (Prodprop14smt2S localx2) =
  le localz localx2
sorted :: List Nat -> P.Bool
sorted Nil = P.True
sorted (Cons localy2 Nil) = P.True
sorted (Cons localy2 (Cons localy22 localxs)) =
  (le localy2 localy22) P.&& (sorted (Cons localy22 localxs))
prodprop14smt2insert2 :: Nat -> List Nat -> List Nat
prodprop14smt2insert2 localx Nil = Cons localx (Nil :: List Nat)
prodprop14smt2insert2 localx (Cons localz2 localxs2) =
  case le localx localz2 of
    P.True -> Cons localx (Cons localz2 localxs2)
    P.False -> Cons localz2 (prodprop14smt2insert2 localx localxs2)
