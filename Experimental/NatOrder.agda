{-# OPTIONS --allow-unsolved-metas #-}

module NatOrder where

open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import Data.Nat.Base
open import Relation.Binary.Structures
open import Data.Nat.Properties using (<-isStrictTotalOrder)

open import OrdSet

instance
 ℕOrder : OrdSet lzero lzero
 OrdSet.Carrier ℕOrder = ℕ
 OrdSet._<_ ℕOrder = _<_
 OrdSet.isStrictTotalOrder ℕOrder = <-isStrictTotalOrder
