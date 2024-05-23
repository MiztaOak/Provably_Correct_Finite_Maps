{-# OPTIONS --erasure #-}

module TreeTest where

open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.Sum using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Nat.Properties using (<-strictTotalOrder)
open import Relation.Binary.Bundles using (StrictTotalOrder)

open import NatOrder
open import Level using (Level; Lift; lower; 0ℓ; _⊔_)
open import Data.Maybe.Base
open import Data.Nat.Base using (ℕ; _+_; suc; zero)
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import Relation.Binary.Definitions
open import Data.Tree.AVL.Map <-strictTotalOrder
open import Data.Tree.AVL <-strictTotalOrder using (tree)
open import Data.Tree.AVL.Map.Membership.Propositional <-strictTotalOrder
open import Data.Tree.AVL.Indexed.Relation.Unary.All <-strictTotalOrder
open import Data.Tree.AVL.Indexed.Relation.Unary.Any <-strictTotalOrder
open import Data.Tree.AVL.Relation.Unary.Any <-strictTotalOrder using (tree)
open import Data.Tree.AVL.Value (setoid ℕ)
open import Data.Tree.AVL.Indexed <-strictTotalOrder
  using (Tree; Key⁺; _<_<_; ⊥⁺<[_]<⊤⁺; _⊕_; _∼_⊔_; joinˡ⁺; [_]; 1#; 0#; [_]ᴿ; ∼+; ∼0; ∼-; joinʳ⁺)
    renaming (insert to insertT)
open StrictTotalOrder <-strictTotalOrder using (compare)

open import Map.BOBMapImp ℕOrder renaming (map to mmap; foldr to mfoldr)
open import Map.MergableMap using (MMap)

open BMapAVLInstance ℕ

private
  variable
    ℓ : Level

SM : Set
SM = Map ℕ

f₁ : ℕ → ℕ → SM → SM
f₁ k v m = insert k v m

open Map.MergableMap.MMap mergeMap
  renaming (insert to minsert; unionWith to munion; unionFoldr to mfun; ∅ to m∅)

MN : Set
MN = AVLMap ℕ

open import Agda.Builtin.List
import Data.List.Base as List
import Function as F

intup : ℕ → MN → MN
intup n m = minsert n n m

mfold : List ℕ → MN
mfold n = List.foldr (λ i → intup i) m∅ n

situp : ℕ → SM → SM
situp n m = insert n n m

sfold : List ℕ → SM
sfold n = List.foldr (λ i → situp i) empty n

mun : MN × MN → MN
mun (a , b) = munion F.const a b

mun2 : MN × MN → MN
mun2 (a , b) = mfun F.const a b

sun : SM × SM → SM
sun (a , b) = union a b

swap : List ℕ → List ℕ
swap [] = []
swap (x ∷ []) = x ∷ []
swap (x ∷ y ∷ lst) = y ∷ x ∷ swap lst

open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Criterion.Main

mtc : ℕ → MN
mtc n = mfold (List.upTo n)

stc : ℕ → SM
stc n = sfold (List.upTo n)

main : IO ⊤
main = defaultMain (
    bgroup "mmap" (
      bench "insert 0..1000" (whnf mtc 1000)
    ∷ bench "union 0..1000 1001..2000" (whnf mun (mfold (List.drop 1000 (List.upTo 2000)) , mfold (List.upTo 1000)))
    ∷ bench "union 0..1000 0..1000" (whnf mun (mfold (swap (List.upTo 1000)) , mfold (swap (List.upTo 1000))))
    ∷ bench "union 0..1000 500..1500" (whnf mun (mfold (swap (List.drop 500 (List.upTo 1500))) , mfold (swap (List.upTo 1000))))
    ∷ bench "union 0..10000 0..10000" (whnf mun (mfold (List.upTo 10000) , mfold (List.upTo 10000)))
    ∷ bench "union 0 0" (whnf mun (mfold [] , mfold []))
    ∷ bench "union 1000 0" (whnf mun (mfold (List.upTo 1000) , mfold []))
    ∷ bench "foldr union 0..1000 1001..2000" (whnf mun2 (mfold (List.drop 1000 (List.upTo 2000)) , mfold (List.upTo 1000)))
    ∷ bench "foldr union 0..1000 0..1000" (whnf mun2 (mfold (swap (List.upTo 1000)) , mfold (swap (List.upTo 1000))))
    ∷ bench "foldr union 0..10000 0..10000" (whnf mun2 (mfold (List.upTo 10000) , mfold (List.upTo 10000)))
    ∷ bench "foldr union 0..1000 500..1500" (whnf mun2 (mfold (swap (List.drop 500 (List.upTo 1500))) , mfold (swap (List.upTo 1000))))
    ∷ bench "foldr union 0 0" (whnf mun2 (mfold [] , mfold []))
    ∷ bench "foldr union 1000 0" (whnf mun2 (mfold (List.upTo 1000) , mfold []))
    ∷ bench "insert 0..1000" (whnf mfold (List.upTo 1000))
    ∷ bench "insert 0..10000" (whnf mfold (List.upTo 10000))
--    ∷ bench "insert 0..100000" (whnf mfold (List.upTo 100000))
--    ∷ bench "insert 0..1000000" (whnf mfold (List.upTo 1000000))
--    ∷ bench "insert 0..10000000" (whnf mfold (List.upTo 10000000))
    ∷ []
    )
  ∷ bgroup "std" (
      bench "insert 0..1000" (whnf sfold (List.upTo 1000))
    ∷ bench "union 0..1000 1001..2000" (whnf sun (sfold (List.drop 1000 (List.upTo 2000)) , sfold (List.upTo 1000)))
    ∷ bench "union 0..1000 0..1000" (whnf sun (sfold (swap F.$ List.drop 1000 (List.upTo 2000)) , sfold (swap F.$ List.upTo 1000)))
    ∷ bench "union 0..1000 500..1500" (whnf sun (sfold (swap (List.drop 500 (List.upTo 1500))) , sfold (swap (List.upTo 1000))))
    ∷ bench "union 0 0" (whnf sun (sfold [] , sfold []))
    ∷ bench "union 1000 0" (whnf sun (sfold (List.upTo 1000) , sfold []))
    ∷ bench "insert 0..1000" (whnf sfold (List.upTo 1000))
    ∷ bench "insert 0..10000" (whnf sfold (List.upTo 10000))
--    ∷ bench "insert 0..100000" (whnf sfold (List.upTo 100000))
--    ∷ bench "insert 0..1000000" (whnf sfold (List.upTo 1000000))
--    ∷ bench "insert 0..10000000" (whnf sfold (List.upTo 10000000))
    ∷ []
    )
  ∷ []
  )
