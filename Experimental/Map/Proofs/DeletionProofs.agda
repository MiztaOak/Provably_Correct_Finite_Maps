{-# OPTIONS --erasure #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet using (OrdSet; toStrictTotalOrder)

module Map.Proofs.DeletionProofs {k ℓ₁ v} (order : OrdSet k ℓ₁) (V : Set v) where
open import Data.Nat.Base using (ℕ; _*_; suc; zero)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality hiding (trans; [_])
open import Level using (Level; _⊔_) renaming (suc to s; zero to z)
open import Data.Product hiding (map)
open import Function.Base
open import Relation.Unary using (Pred)
open import Data.Maybe.Base hiding (map)
open import Data.Sum hiding (map)
open import Relation.Nullary using (¬_)
open import Relation.Binary.Definitions

open import Prelude
open import Map.BOBMap order as BOB
open StrictTotalOrder (toStrictTotalOrder order) renaming (Carrier to Key)
open import Map.Proofs.Proofs order V


---------------------------------------------------------------------------------
-- del-∈
---------------------------------------------------------------------------------
notInLeft : ∀ {l : Key⁺} {h : ℕ}
            (k : Key)
            (m : BOBMap V l [ k ] h)
            → k ∉ m
notInLeft k leaf ()
notInLeft k (node .(k , _) lm rm b) (here tt) = ⊥-elim (irrefl⁺ [ k ] (mklim rm))
notInLeft k (node p lm rm b) (left ⦃ ord ⦄ prf) = ⊥-elim (asym [ ord ]-lower [ mklim rm ]-lower)
notInLeft k (node p lm rm b) (right prf) = notInLeft k rm prf

notInRight : ∀ {u : Key⁺} {h : ℕ}
             (k : Key)
             (m : BOBMap V [ k ] u h)
             → k ∉ m
notInRight k leaf ()
notInRight k (node p lm rm b) (here tt) = ⊥-elim (irrefl⁺ [ k ] (mklim lm))
notInRight k (node p lm rm b) (left prf) = notInRight k lm prf
notInRight k (node p lm rm b) (right ⦃ ord ⦄ prf) = ⊥-elim (asym [ ord ]-lower [ mklim lm ]-lower)

inRaise : ∀ {l y u : Key⁺} {h : ℕ}
          ⦃ @erased y<u : y <⁺ u ⦄
          {k : Key}
          {m : BOBMap V l y h}
          → k ∈ m
          → k ∈ (raise m)
inRaise {k = k} {leaf} ()
inRaise ⦃ y<u = y<u ⦄ {k} {node p l r b} (here tt) = here ⦃ k≤u = trans⁺ [ k ] (mklim r) y<u ⦄ tt
inRaise {k = k} {node p l r b} (left prf) = left prf
inRaise {k = k} {node p l r b} (right prf) = right (inRaise prf)

inRaise' : ∀ {l y u : Key⁺} {h : ℕ}
          ⦃ @erased y<u : y <⁺ u ⦄
          {k : Key}
          {m : BOBMap V l y h}
          → k ∈ (raise m)
          → k ∈ m
inRaise' {k = k} {leaf} ()
inRaise' {k = k} {node p l r b} (here tt) = here ⦃ k≤u = mklim r ⦄ tt
inRaise' {k = k} {node p l r b} (left prf) = left prf
inRaise' {k = k} {node p l r b} (right prf) = right (inRaise' prf)

inᴸ-joinᴸ⁻ : ∀ {l u : Key⁺} {hl hr h}
            {k : Key}
            {p : Key × V}
            ⦃ @erased l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ @erased p<u : [ proj₁ p ] <⁺ u ⦄
            (lt⁻ : ∃ λ i → BOBMap V l [ proj₁ p ] pred[ i ⊕ hl ])
            (rt : BOBMap V [ proj₁ p ] u hr)
            (bal : hl ~ hr ⊔ h)
            → @erased [ k ] <⁺ [ proj₁ p ]
            → k ∈ (proj₂ (joinˡ⁻ p lt⁻ rt bal))
            → k ∈ proj₂ lt⁻
inᴸ-joinᴸ⁻ {hl = zero} {k = k} (0# , lt) rt bal ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
inᴸ-joinᴸ⁻ {hl = zero} {k = k} (0# , lt) rt bal ord (right ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴸ⁻ {hl = zero} {k = k} (1# , lt) rt bal ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
inᴸ-joinᴸ⁻ {hl = zero} {k = k} (1# , lt) rt bal ord (right ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴸ⁻ {hl = suc hl} {k = k} {p} (0# , lt) rt ~+ ord prf = inᴸ-joinᴿ⁺ k p lt (1# , rt) ~+ ord prf
inᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (0# , lt) rt ~- ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
inᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (0# , lt) rt ~- ord (left prf) = prf
inᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (0# , lt) rt ~- ord (right ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (0# , lt) rt ~0 ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
inᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (0# , lt) rt ~0 ord (left prf) = prf
inᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (0# , lt) rt ~0 ord (right ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (1# , lt) rt bal ord (here x) = ⊥-elim (irrefl⁺ [ k ] ord)
inᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (1# , lt) rt bal ord (left prf) = prf
inᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (1# , lt) rt bal ord (right ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)

inᴿ-joinᴿ⁻ : ∀ {l u : Key⁺} {hl hr h}
            {k : Key}
            {p : Key × V}
            ⦃ @erased l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ @erased p<u : [ proj₁ p ] <⁺ u ⦄
            (lt : BOBMap V l [ proj₁ p ] hl)
            (rt⁻ : ∃ λ i → BOBMap V [ proj₁ p ] u pred[ i ⊕ hr ])
            (bal : hl ~ hr ⊔ h)
            → @erased [ proj₁ p ] <⁺ [ k ]
            → k ∈ (proj₂ (joinʳ⁻ p lt rt⁻ bal))
            → k ∈ proj₂ rt⁻
inᴿ-joinᴿ⁻ {hr = zero} {k = k} lt (0# , rt) bal ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
inᴿ-joinᴿ⁻ {hr = zero} {k = k} lt (0# , rt) bal ord (left ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴿ⁻ {hr = zero} {k = k} lt (1# , rt) bal ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
inᴿ-joinᴿ⁻ {hr = zero} {k = k} lt (1# , rt) bal ord (left ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~+ ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
inᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~+ ord (left ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~+ ord (right prf) = prf
inᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~0 ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
inᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~0 ord (left ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~0 ord (right prf) = prf
inᴿ-joinᴿ⁻ {hr = suc _} {k = k} {p} lt (0# , rt) ~- ord prf = inᴿ-joinᴸ⁺ k p (1# , lt) rt ~- ord prf
inᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (1# , rt) bal ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
inᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (1# , rt) bal ord (left ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (1# , rt) bal ord (right prf) = prf

inᴸ-joinᴿ⁻ : ∀ {l u : Key⁺} {hl hr h}
            {k : Key}
            {p : Key × V}
            ⦃ @erased l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ @erased p<u : [ proj₁ p ] <⁺ u ⦄
            (lt : BOBMap V l [ proj₁ p ] hl)
            (rt⁻ : ∃ λ i → BOBMap V [ proj₁ p ] u pred[ i ⊕ hr ])
            (bal : hl ~ hr ⊔ h)
            → @erased [ k ] <⁺ [ proj₁ p ]
            → k ∈ (proj₂ (joinʳ⁻ p lt rt⁻ bal))
            → k ∈ lt
inᴸ-joinᴿ⁻ {hr = zero} {k = k} lt (0# , rt) bal ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
inᴸ-joinᴿ⁻ {hr = zero} {k = k} lt (0# , rt) bal ord (left prf) = prf
inᴸ-joinᴿ⁻ {hr = zero} {k = k} lt (1# , rt) bal ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
inᴸ-joinᴿ⁻ {hr = zero} {k = k} lt (1# , rt) bal ord (left prf) = prf
inᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~+ ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
inᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~+ ord (left prf) = prf
inᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~+ ord (right ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~0 ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
inᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~0 ord (left prf) = prf
inᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~0 ord (right ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴿ⁻ {hr = suc _} {k = k} {p} lt (0# , rt) ~- ord prf = inᴸ-joinᴸ⁺ k p (1# , lt) rt ~- ord prf
inᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (1# , rt) bal ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
inᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (1# , rt) bal ord (left prf) = prf
inᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (1# , rt) bal ord (right ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)

del-∈ : ∀ {l u : Key⁺} {h : ℕ}
        (k : Key) (m : BOBMap V l u h)
        ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
        → k ∈ m
        → k ∉ proj₂ (delete k m)
del-∈ k leaf () ∉dM
del-∈ k (node p lm rm b) ∈M ∉dM with compare k (proj₁ p)
... | tri< a _ _ = del-∈ k lm ⦃ k<u = [ a ]ᴿ ⦄ (anyLeft a ∈M) prfᴸ
  where
    prfᴸ = inᴸ-joinᴸ⁻ ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ (delete k ⦃ p≤u = [ a ]ᴿ ⦄ lm) rm b [ a ]ᴿ ∉dM
... | tri≈ _ refl _ = notHere {rm = rm} (notInLeft k lm) ∉dM
  where
    notHere : ∀ {l u : Key⁺} {hl hr h : ℕ}
              {k : Key}
              {lm : BOBMap V l [ k ] hl}
              {rm : BOBMap V [ k ] u hr}
              {b : hl ~ hr ⊔ h}
              → ¬ k ∈ lm
              → ¬ (k ∈ proj₂ (join lm rm b))
    notHere {k = k} {lm} {leaf} {~- } ¬lm prf = ¬lm (inRaise' prf)
    notHere {k = k} {lm} {leaf} {~0} ¬lm ()
    notHere {l} {k = k} {lm} rm@{node _ _ _ _} {b} ¬lm prf with uncons rm
    ... | cons head l<u tail with
      inᴸ-joinᴿ⁻ ⦃ trans⁺ l (mklim lm) l<u ⦄ ⦃ mklim (proj₂ tail) ⦄ (raise ⦃ l<u ⦄ lm) tail b l<u prf
    ... | prfᴸ = ¬lm (inRaise' ⦃ l<u ⦄ prfᴸ)
... | tri> _ _ c = del-∈ k rm ⦃ [ c ]ᴿ ⦄ (anyRight c ∈M) prfᴿ
  where
    prfᴿ = inᴿ-joinᴿ⁻ ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lm (delete k ⦃ [ c ]ᴿ ⦄ rm) b [ c ]ᴿ ∉dM

---------------------------------------------------------------------------------
-- del-safe
---------------------------------------------------------------------------------
del-safe : ∀ {l u : Key⁺} {h : ℕ} (k k' : Key) {v : V} (m : BOBMap V l u h)
           ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
           → k' ↦ v ∈ m
           → k ≢ k'
           → k' ↦ v ∈ proj₂ (delete k m)
del-safe k k' leaf () nEq
del-safe k k' (node .(k' , _) lm rm b) (here refl) nEq with compare k k'
... | tri< a _ _ = {!!}
... | tri≈ _ refl _ = ⊥-elim (nEq refl)
... | tri> _ _ c = {!!}
del-safe k k' (node p lm rm b) (left prf) nEq with compare k (proj₁ p)
... | tri< a _ _ = {!!}
... | tri≈ _ refl _ = {!!}
... | tri> _ _ c = {!!}
del-safe k k' (node p lm rm b) (right prf) nEq with compare k (proj₁ p)
... | tri< a _ _ = {!!}
... | tri≈ _ refl _ = {!!}
... | tri> _ _ c = {!!}

---------------------------------------------------------------------------------
-- del-∉
---------------------------------------------------------------------------------
del-∉del⊆ : ∀ {l u : Key⁺} {h : ℕ} (k : Key)
        ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
        (m : BOBMap V l u h)
        → k ∉ m
        → proj₂ (delete k m) ⊆ m
del-∉del⊆ k leaf prf k' v ()
del-∉del⊆ k (node p lm rm bal) prf k' v prf' = {!!}

∈Contradiction : ∀ {l u : Key⁺} {h : ℕ} {m : BOBMap V l u h} {k k' : Key}
                 → k ∉ m
                 → k' ∈ m
                 → k ≢ k'
∈Contradiction {k = k} {k'} prf prf' with compare k k'
... | tri< _ ¬b _ = ¬b
... | tri≈ _ refl _ = ⊥-elim (prf prf')
... | tri> _ ¬b _ = ¬b

del-∉m⊆ : ∀ {l u : Key⁺} {h : ℕ} (k : Key)
        ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
        (m : BOBMap V l u h)
        → k ∉ m
        → m ⊆ proj₂ (delete k m)
del-∉m⊆ k m prf k' v prf' = del-safe k k' m prf' (∈Contradiction prf (↦∈To∈ prf'))

del-∉ : ∀ {l u : Key⁺} {h : ℕ} (k : Key)
        ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
        (m : BOBMap V l u h)
        → k ∉ m
        → proj₂ (delete k m) ≐ m
del-∉ k m prf = (del-∉del⊆ k m prf) , (del-∉m⊆ k m prf)

-- -}
-- -}
-- -}
-- -}
-- -}
