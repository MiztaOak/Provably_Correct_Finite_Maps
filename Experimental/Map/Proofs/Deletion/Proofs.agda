{-# OPTIONS --erasure #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet using (OrdSet; toStrictTotalOrder)

module Map.Proofs.Deletion.Proofs {k ℓ₁ v} (order : OrdSet k ℓ₁) (V : Set v) where
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
open import Map.Proofs.Insertion.Helpers order V using (inᴸ-joinᴿ⁺; inᴿ-joinᴸ⁺; inᴸ-joinᴸ⁺)
open import Map.Proofs.Deletion.Helpers order V

---------------------------------------------------------------------------------
-- del-∈
---------------------------------------------------------------------------------
∈ᴸ-joinᴸ⁻ : ∀ {l u : Key⁺} {hl hr h}
            {k : Key}
            {p : Key × V}
            ⦃ @erased l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ @erased p<u : [ proj₁ p ] <⁺ u ⦄
            (lt⁻ : ∃ λ i → BOBMap V l [ proj₁ p ] pred[ i ⊕ hl ])
            (rt : BOBMap V [ proj₁ p ] u hr)
            (bal : hl ~ hr ⊔ h)
            → @erased [ k ] <⁺ [ proj₁ p ]
            → k ∈ (proj₂ (joinˡ⁻ p lt⁻ rt bal))
            → k ∈ proj₂ lt⁻
∈ᴸ-joinᴸ⁻ {hl = zero} {k = k} (0# , lt) rt bal ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
∈ᴸ-joinᴸ⁻ {hl = zero} {k = k} (0# , lt) rt bal ord (right ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
∈ᴸ-joinᴸ⁻ {hl = zero} {k = k} (1# , lt) rt bal ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
∈ᴸ-joinᴸ⁻ {hl = zero} {k = k} (1# , lt) rt bal ord (right ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
∈ᴸ-joinᴸ⁻ {hl = suc hl} {k = k} {p} (0# , lt) rt ~+ ord prf = inᴸ-joinᴿ⁺ lt (1# , rt) ~+ ord prf
∈ᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (0# , lt) rt ~- ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
∈ᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (0# , lt) rt ~- ord (left prf) = prf
∈ᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (0# , lt) rt ~- ord (right ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
∈ᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (0# , lt) rt ~0 ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
∈ᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (0# , lt) rt ~0 ord (left prf) = prf
∈ᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (0# , lt) rt ~0 ord (right ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
∈ᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (1# , lt) rt bal ord (here x) = ⊥-elim (irrefl⁺ [ k ] ord)
∈ᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (1# , lt) rt bal ord (left prf) = prf
∈ᴸ-joinᴸ⁻ {hl = suc hl} {k = k} (1# , lt) rt bal ord (right ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)

∈ᴿ-joinᴿ⁻ : ∀ {l u : Key⁺} {hl hr h}
            {k : Key}
            {p : Key × V}
            ⦃ @erased l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ @erased p<u : [ proj₁ p ] <⁺ u ⦄
            (lt : BOBMap V l [ proj₁ p ] hl)
            (rt⁻ : ∃ λ i → BOBMap V [ proj₁ p ] u pred[ i ⊕ hr ])
            (bal : hl ~ hr ⊔ h)
            → @erased [ proj₁ p ] <⁺ [ k ]
            → k ∈ (proj₂ (joinʳ⁻ p lt rt⁻ bal))
            → k ∈ proj₂ rt⁻
∈ᴿ-joinᴿ⁻ {hr = zero} {k = k} lt (0# , rt) bal ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
∈ᴿ-joinᴿ⁻ {hr = zero} {k = k} lt (0# , rt) bal ord (left ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
∈ᴿ-joinᴿ⁻ {hr = zero} {k = k} lt (1# , rt) bal ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
∈ᴿ-joinᴿ⁻ {hr = zero} {k = k} lt (1# , rt) bal ord (left ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
∈ᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~+ ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
∈ᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~+ ord (left ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
∈ᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~+ ord (right prf) = prf
∈ᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~0 ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
∈ᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~0 ord (left ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
∈ᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~0 ord (right prf) = prf
∈ᴿ-joinᴿ⁻ {hr = suc _} {k = k} {p} lt (0# , rt) ~- ord prf = inᴿ-joinᴸ⁺ (1# , lt) rt ~- ord prf
∈ᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (1# , rt) bal ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
∈ᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (1# , rt) bal ord (left ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
∈ᴿ-joinᴿ⁻ {hr = suc _} {k = k} lt (1# , rt) bal ord (right prf) = prf

∈ᴸ-joinᴿ⁻ : ∀ {l u : Key⁺} {hl hr h}
            {k : Key}
            {p : Key × V}
            ⦃ @erased l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ @erased p<u : [ proj₁ p ] <⁺ u ⦄
            (lt : BOBMap V l [ proj₁ p ] hl)
            (rt⁻ : ∃ λ i → BOBMap V [ proj₁ p ] u pred[ i ⊕ hr ])
            (bal : hl ~ hr ⊔ h)
            → @erased [ k ] <⁺ [ proj₁ p ]
            → k ∈ (proj₂ (joinʳ⁻ p lt rt⁻ bal))
            → k ∈ lt
∈ᴸ-joinᴿ⁻ {hr = zero} {k = k} lt (0# , rt) bal ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
∈ᴸ-joinᴿ⁻ {hr = zero} {k = k} lt (0# , rt) bal ord (left prf) = prf
∈ᴸ-joinᴿ⁻ {hr = zero} {k = k} lt (1# , rt) bal ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
∈ᴸ-joinᴿ⁻ {hr = zero} {k = k} lt (1# , rt) bal ord (left prf) = prf
∈ᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~+ ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
∈ᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~+ ord (left prf) = prf
∈ᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~+ ord (right ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
∈ᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~0 ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
∈ᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~0 ord (left prf) = prf
∈ᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (0# , rt) ~0 ord (right ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
∈ᴸ-joinᴿ⁻ {hr = suc _} {k = k} {p} lt (0# , rt) ~- ord prf = inᴸ-joinᴸ⁺ (1# , lt) rt ~- ord prf
∈ᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (1# , rt) bal ord (here tt) = ⊥-elim (irrefl⁺ [ k ] ord)
∈ᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (1# , rt) bal ord (left prf) = prf
∈ᴸ-joinᴿ⁻ {hr = suc _} {k = k} lt (1# , rt) bal ord (right ⦃ ord' ⦄ prf) =
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
    prfᴸ = ∈ᴸ-joinᴸ⁻ ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ (delete k ⦃ p≤u = [ a ]ᴿ ⦄ lm) rm b [ a ]ᴿ ∉dM
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
      ∈ᴸ-joinᴿ⁻ ⦃ trans⁺ l (mklim lm) l<u ⦄ ⦃ mklim (proj₂ tail) ⦄ (raise ⦃ l<u ⦄ lm) tail b l<u prf
    ... | prfᴸ = ¬lm (inRaise' ⦃ l<u ⦄ prfᴸ)
... | tri> _ _ c = del-∈ k rm ⦃ [ c ]ᴿ ⦄ (anyRight c ∈M) prfᴿ
  where
    prfᴿ = ∈ᴿ-joinᴿ⁻ ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lm (delete k ⦃ [ c ]ᴿ ⦄ rm) b [ c ]ᴿ ∉dM

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
... | tri< a _ _ = herejoinᴸ⁻ (delete k ⦃ p≤u = [ a ]ᴿ ⦄ lm) rm b
... | tri≈ _ refl _ = ⊥-elim (nEq refl)
... | tri> _ _ c = herejoinᴿ⁻ lm (delete k ⦃ [ c ]ᴿ ⦄ rm) b
del-safe k k' (node p lm rm b) (left ⦃ k'<p ⦄ prf) nEq with compare k (proj₁ p)
... | tri< a _ _ = anyᴸ-joinᴸ⁻ lm⁻ rm b k'<p prfᴸ
  where
    prfᴸ = del-safe k k' lm ⦃ k<u = [ a ]ᴿ ⦄ prf nEq
    lm⁻ = delete k ⦃ p≤u = [ a ]ᴿ ⦄ lm
... | tri≈ _ refl _ = anyJoinᴸ lm rm b prf [ k'<p ]-lower
... | tri> _ _ c = anyᴸ-joinᴿ⁻ lm rm⁻ b k'<p prf
  where
    rm⁻ = delete k ⦃ [ c ]ᴿ ⦄ rm
del-safe k k' (node p lm rm b) (right ⦃ p<k' ⦄ prf) nEq with compare k (proj₁ p)
... | tri< a _ _ = anyᴿ-joinᴸ⁻ lm⁻ rm b p<k' prf
  where
    lm⁻ = delete k ⦃ p≤u = [ a ]ᴿ ⦄ lm
... | tri≈ _ refl _ = anyJoinᴿ lm rm b prf p<k'
... | tri> _ _ c = anyᴿ-joinᴿ⁻ lm rm⁻ b p<k' prfᴿ
  where
    prfᴿ = del-safe k k' rm ⦃ [ c ]ᴿ ⦄ prf nEq
    rm⁻ = delete k ⦃ [ c ]ᴿ ⦄ rm

notInJoin : ∀ {l u : Key⁺} {hl hr h : ℕ}
  → (k : Key)
  → {v : V}
  → (lm : BOBMap V l [ k ] hl)
  → (rm : BOBMap V [ k ] u hr)
  → (bal : hl ~ hr ⊔ h)
  → ¬ (k ↦ v ∈ proj₂ (join lm rm bal))
notInJoin k lm leaf ~0 prf = notInLeft k lm (inRaise' (↦∈To∈ prf))
notInJoin k lm leaf ~- prf = notInLeft k lm (inRaise' (↦∈To∈ prf))
notInJoin k lm rm@(node _ _ _ _) bal prf with uncons rm
... | cons head l<u tail = notInLeft k lm (inRaise' ⦃ l<u ⦄ (↦∈To∈ prf'))
  where
    prf' = inᴸ-joinᴿ⁻ (raise ⦃ l<u ⦄ lm) tail bal l<u prf

del-safe' : ∀ {l u : Key⁺} {h : ℕ} (k : Key) {v : V} (m : BOBMap V l u h)
           ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
           → ¬ (k ↦ v ∈ proj₂ (delete k m))
del-safe' k leaf ()
del-safe' k (node p lm rm bal) prf with compare k (proj₁ p)
... | tri< k<p _ _ =
  del-safe' k lm ⦃ k<u = [ k<p ]ᴿ ⦄ (inᴸ-joinᴸ⁻ (delete k ⦃ p≤u = [ k<p ]ᴿ ⦄ lm) rm bal [ k<p ]ᴿ prf)
... | tri> _ _ p<k =
  del-safe' k rm ⦃ [ p<k ]ᴿ ⦄ (inᴿ-joinᴿ⁻ lm (delete k ⦃ [ p<k ]ᴿ ⦄ rm) bal [ p<k ]ᴿ prf)
... | tri≈ _ refl _ = notInJoin k lm rm bal prf

---------------------------------------------------------------------------------
-- del-∉
---------------------------------------------------------------------------------
del-∉del⊆ : ∀ {l u : Key⁺} {h : ℕ} (k : Key)
        ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
        (m : BOBMap V l u h)
        → k ∉ m
        → proj₂ (delete k m) ⊆ m
del-∉del⊆ k leaf prf k' v ()
del-∉del⊆ k (node p lm rm bal) prf k' v prf' with compare k (proj₁ p)
... | tri≈ _ refl _ = ⊥-elim (prf (here tt))
del-∉del⊆ k (node p lm rm bal) prf k' v prf' | tri< k<p _ _ with compare k' (proj₁ p)
... | tri< k'<p _ _ = left ⦃ [ k'<p ]ᴿ ⦄ (del-∉del⊆ k ⦃ k<u = [ k<p ]ᴿ ⦄ lm (∉Left k<p prf) k' v prfᴸ)
  where
    lm⁻ = delete k ⦃ p≤u = [ k<p ]ᴿ ⦄ lm
    prfᴸ = inᴸ-joinᴸ⁻ lm⁻ rm bal [ k'<p ]ᴿ prf'
... | tri≈ _ refl _ = here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ prfC
  where
    lm⁻ = delete k ⦃ p≤u = [ k<p ]ᴿ ⦄ lm
    prfC = inC-joinᴸ⁻ lm⁻ rm bal prf'
... | tri> _ _ p<k' = right ⦃ [ p<k' ]ᴿ ⦄ prfᴿ
  where
    lm⁻ = delete k ⦃ p≤u = [ k<p ]ᴿ ⦄ lm
    prfᴿ = inᴿ-joinᴸ⁻ lm⁻ rm bal [ p<k' ]ᴿ prf'
del-∉del⊆ k (node p lm rm bal) prf k' v prf' | tri> _ _ p<k with compare k' (proj₁ p)
... | tri< k'<p _ _ = left ⦃ [ k'<p ]ᴿ ⦄ prfᴸ
  where
    rm⁻ = delete k ⦃ [ p<k ]ᴿ ⦄ rm
    prfᴸ = inᴸ-joinᴿ⁻ lm rm⁻ bal [ k'<p ]ᴿ prf'
... | tri≈ _ refl _ = here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ prfC
  where
    rm⁻ = delete k ⦃ [ p<k ]ᴿ ⦄ rm
    prfC = inC-joinᴿ⁻ lm rm⁻ bal prf'
... | tri> _ _ p<k' = right ⦃ [ p<k' ]ᴿ ⦄ (del-∉del⊆ k ⦃ [ p<k ]ᴿ ⦄ rm (∉Right p<k prf) k' v prfᴿ)
  where
    rm⁻ = delete k ⦃ [ p<k ]ᴿ ⦄ rm
    prfᴿ = inᴿ-joinᴿ⁻ lm rm⁻ bal [ p<k' ]ᴿ prf'


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

---------------------------------------------------------------------------------
-- proof that delete does not add any elements to the map
---------------------------------------------------------------------------------
del-noAdd : ∀ {l u : Key⁺} {h : ℕ} (k k' : Key) {v : V}
  ⦃ @erased l<k : l <⁺ [ k' ] ⦄ ⦃ @erased k<u : [ k' ] <⁺ u ⦄
  → (m : BOBMap V l u h)
  → k ↦ v ∈ proj₂ (delete k' m)
  → k ↦ v ∈ m
del-noAdd k k' leaf ()
del-noAdd k k' (node p lm rm bal) prf with compare k k'
del-noAdd k k' (node p lm rm bal) prf | tri< k<k' _ _ with compare k' (proj₁ p)
... | tri< k'<p _ _ = left ⦃ [ k<p ]ᴿ ⦄ (del-noAdd k k' ⦃ k<u = [ k'<p ]ᴿ ⦄ lm prf')
  where
    k<p = trans k<k' k'<p
    prf' = inᴸ-joinᴸ⁻ (delete k' ⦃ p≤u = [ k'<p ]ᴿ ⦄ lm) rm bal [ k<p ]ᴿ prf
... | tri≈ _ refl _ with compare k (proj₁ p)
... | tri< k<p _ _ = left ⦃ [ k<p ]ᴿ ⦄ (inJoinᴸ lm rm bal prf k<p)
... | tri≈ _ refl _ = ⊥-elim (notInJoin k lm rm bal prf)
... | tri> _ _ p<k = right ⦃ [ p<k ]ᴿ ⦄ (inJoinᴿ lm rm bal prf p<k)
del-noAdd k k' (node p lm rm bal) prf | tri< k<k' _ _ | tri> _ _ p<k' with compare k (proj₁ p)
... | tri< k<p _ _  = left ⦃ [ k<p ]ᴿ ⦄ prf'
  where
    prf' = inᴸ-joinᴿ⁻ lm (delete k' ⦃ [ p<k' ]ᴿ ⦄ rm) bal [ k<p ]ᴿ prf
... | tri≈ _ refl _ rewrite inC-joinᴿ⁻ lm (delete k' ⦃ [ p<k' ]ᴿ ⦄ rm) bal prf =
  here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ refl
... | tri> _ _ p<k = right ⦃ [ p<k ]ᴿ ⦄ (del-noAdd k k' ⦃ [ p<k' ]ᴿ ⦄ rm prf')
  where
    prf' = inᴿ-joinᴿ⁻ lm (delete k' ⦃ [ p<k' ]ᴿ ⦄ rm) bal [ p<k ]ᴿ prf
del-noAdd k k' (node p lm rm bal) prf | tri≈ _ refl _ = ⊥-elim (del-safe' k' (node p lm rm bal) prf)
del-noAdd k k' (node p lm rm bal) prf | tri> _ _ k'<k with compare k' (proj₁ p)
... | tri> _ _ p<k' = right ⦃ [ p<k ]ᴿ ⦄ (del-noAdd k k' ⦃ [ p<k' ]ᴿ ⦄ rm prf')
  where
    p<k = trans p<k' k'<k
    prf' = inᴿ-joinᴿ⁻ lm (delete k' ⦃ [ p<k' ]ᴿ ⦄ rm) bal [ p<k ]ᴿ prf
... | tri< k'<p _ _ with compare k (proj₁ p)
... | tri< k<p _ _ = left ⦃ [ k<p ]ᴿ ⦄ (del-noAdd k k' ⦃ k<u = [ k'<p ]ᴿ ⦄ lm prf')
  where
    prf' = inᴸ-joinᴸ⁻ (delete k' ⦃ p≤u = [ k'<p ]ᴿ ⦄ lm) rm bal [ k<p ]ᴿ prf
... | tri≈ _ refl _ rewrite inC-joinᴸ⁻ (delete k' ⦃ p≤u = [ k'<p ]ᴿ ⦄ lm) rm bal prf =
  here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ refl
... | tri> _ _ p<k = right ⦃ [ p<k ]ᴿ ⦄ prf'
  where
    prf' = inᴿ-joinᴸ⁻ (delete k' ⦃ p≤u = [ k'<p ]ᴿ ⦄ lm) rm bal [ p<k ]ᴿ prf
del-noAdd k k' (node p lm rm bal) prf | tri> _ _ k'<k | tri≈ _ refl _ with compare k (proj₁ p)
... | tri< k<p _ _ = left ⦃ [ k<p ]ᴿ ⦄ (inJoinᴸ lm rm bal prf k<p)
... | tri≈ _ refl _ = ⊥-elim (notInJoin (proj₁ p) lm rm bal prf)
... | tri> _ _ p<k = right ⦃ [ p<k ]ᴿ ⦄ (inJoinᴿ lm rm bal prf p<k)

---------------------------------------------------------------------------------
-- delete commutativity
---------------------------------------------------------------------------------
isEq? : ∀ (x y : Key) → x ≡ y ⊎ x ≢ y
isEq? x y with compare x y
... | tri< _ nEq _  = inj₂ nEq
... | tri≈ _ refl _ = inj₁ refl
... | tri> _ nEq _  = inj₂ nEq

delete-joinR→R : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (x y z : Key)
    (p : Key × V)
    {v : V}
    ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ p<x : [ proj₁ p ] <⁺ [ x ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
    ⦃ l<y : l <⁺ [ y ] ⦄ ⦃ p<y : [ proj₁ p ] <⁺ [ y ] ⦄ ⦃ y<u : [ y ] <⁺ u ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → z ↦ v ∈ (proj₂ (delete x (proj₂ (joinʳ⁻ p lt (delete y rt) bal))))
    → z ↦ v ∈ (proj₂ (delete y (proj₂ (joinʳ⁻ p lt (delete x rt) bal))))
delete-joinR→R x y z p lt rt bal prf with delete y rt
... | rtʸ with joinʳ⁻ p lt rtʸ bal in eqJoin
... | rt⁺ with del-noAdd z x (proj₂ rt⁺) prf
... | prf' with compare z x
... | tri≈ _ refl _ = ⊥-elim (del-safe' x (proj₂ rt⁺) prf)
... | tri< z<x _ _ rewrite sym eqJoin = {!prf'!}
... | tri> _ _ x<z rewrite sym eqJoin = {!prf'!}

delete-joinL→L : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (x y z : Key)
    (p : Key × V)
    {v : V}
    ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ x<p : [ x ] <⁺ [ proj₁ p ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
    ⦃ l<y : l <⁺ [ y ] ⦄ ⦃ y<p : [ y ] <⁺ [ proj₁ p ] ⦄ ⦃ y<u : [ y ] <⁺ u ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → z ↦ v ∈ (proj₂ (delete x (proj₂ (joinˡ⁻ p (delete y lt) rt bal))))
    → z ↦ v ∈ (proj₂ (delete y (proj₂ (joinˡ⁻ p (delete x lt) rt bal))))
delete-joinL→R : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (x y z : Key)
    (p : Key × V)
    {v : V}
    ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ p<x : [ proj₁ p ] <⁺ [ x ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
    ⦃ l<y : l <⁺ [ y ] ⦄ ⦃ y<p : [ y ] <⁺ [ proj₁ p ] ⦄ ⦃ y<u : [ y ] <⁺ u ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → z ↦ v ∈ (proj₂ (delete x (proj₂ (joinˡ⁻ p (delete y lt) rt bal))))
    → z ↦ v ∈ (proj₂ (delete y (proj₂ (joinʳ⁻ p lt (delete x rt) bal))))
delete-joinR→L : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (x y z : Key)
    (p : Key × V)
    {v : V}
    ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ x<p : [ x ] <⁺ [ proj₁ p ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
    ⦃ l<y : l <⁺ [ y ] ⦄ ⦃ p<y : [ proj₁ p ] <⁺ [ y ] ⦄ ⦃ y<u : [ y ] <⁺ u ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → z ↦ v ∈ (proj₂ (delete x (proj₂ (joinʳ⁻ p lt (delete y rt) bal))))
    → z ↦ v ∈ (proj₂ (delete y (proj₂ (joinˡ⁻ p (delete x lt) rt bal))))

del-comm : ∀ {l u : Key⁺} {h : ℕ}
  → (x y k : Key)
  → {v : V}
  ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
  ⦃ l<y : l <⁺ [ y ] ⦄ ⦃ y<u : [ y ] <⁺ u ⦄
  → (m : BOBMap V l u h)
  → k ↦ v ∈ proj₂ (delete x (proj₂ (delete y m)))
  → k ↦ v ∈ proj₂ (delete y (proj₂ (delete x m)))
del-comm x y k (node p lm rm bal) prf with compare x y
... | tri≈ _ refl _ = prf
del-comm x y k (node p lm rm bal) prf | tri< x<y _ _ with compare y (proj₁ p)
... | tri< y<p _ _ with compare x (proj₁ p)
... | tri< x<p _ _ = delete-joinL→L x y k p ⦃ x<p = [ x<p ]ᴿ ⦄ ⦃ y<p = [ y<p ]ᴿ ⦄ lm rm bal prf
... | tri≈ _ refl _ = {!!}
... | tri> _ _ p<x = delete-joinL→R x y k p ⦃ p<x = [ p<x ]ᴿ ⦄ ⦃ y<p = [ y<p ]ᴿ ⦄ lm rm bal prf
del-comm x y k (node p lm rm bal) prf | tri< x<y _ _ | tri≈ _ refl _ with compare x (proj₁ p)
... | tri< x<p _ _ = {!!}
... | tri≈ _ refl _ = prf
... | tri> _ _ p<x = {!!}
del-comm x y k (node p lm rm bal) prf | tri< x<y _ _ | tri> _ _ p<y with compare x (proj₁ p)
... | tri< x<p _ _ = delete-joinR→L x y k p ⦃ x<p = [ x<p ]ᴿ ⦄ ⦃ p<y = [ p<y ]ᴿ ⦄ lm rm bal prf
... | tri≈ _ refl _ = {!!}
... | tri> _ _ p<x = delete-joinR→R x y k p ⦃ p<x = [ p<x ]ᴿ ⦄ ⦃ p<y = [ p<y ]ᴿ ⦄ lm rm bal prf
del-comm x y k (node p lm rm bal) prf | tri> _ _ y<x with compare y (proj₁ p)
... | tri< y<p _ _ with compare x (proj₁ p)
... | tri< x<p _ _ = delete-joinL→L x y k p ⦃ x<p = [ x<p ]ᴿ ⦄ ⦃ y<p = [ y<p ]ᴿ ⦄ lm rm bal prf
... | tri≈ _ refl _ = {!!}
... | tri> _ _ p<x = delete-joinL→R x y k p ⦃ p<x = [ p<x ]ᴿ ⦄ ⦃ y<p = [ y<p ]ᴿ ⦄ lm rm bal prf
del-comm x y k (node p lm rm bal) prf | tri> _ _ y<x | tri≈ _ refl _ with compare x (proj₁ p)
... | tri< x<p _ _ = {!!}
... | tri≈ _ refl _ = prf
... | tri> _ _ p<x = {!!}
del-comm x y k (node p lm rm bal) prf | tri> _ _ y<x | tri> _ _ p<y with compare x (proj₁ p)
... | tri< x<p _ _ = delete-joinR→L x y k p ⦃ x<p = [ x<p ]ᴿ ⦄ ⦃ p<y = [ p<y ]ᴿ ⦄ lm rm bal prf
... | tri≈ _ refl _ = {!!}
... | tri> _ _ p<x = delete-joinR→R x y k p ⦃ p<x = [ p<x ]ᴿ ⦄ ⦃ p<y = [ p<y ]ᴿ ⦄ lm rm bal prf
-- -}
-- -}
-- -}
-- -}
-- -}
