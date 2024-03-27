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
∈ᴸ-joinᴸ⁻ {hl = suc hl} {k = k} {p} (0# , lt) rt ~+ ord prf = inᴸ-joinᴿ⁺ k p lt (1# , rt) ~+ ord prf
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
∈ᴿ-joinᴿ⁻ {hr = suc _} {k = k} {p} lt (0# , rt) ~- ord prf = inᴿ-joinᴸ⁺ k p (1# , lt) rt ~- ord prf
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
∈ᴸ-joinᴿ⁻ {hr = suc _} {k = k} {p} lt (0# , rt) ~- ord prf = inᴸ-joinᴸ⁺ k p (1# , lt) rt ~- ord prf
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
anyᴿ-joinᴿ⁻ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k : Key}
    {v : V}
    {p : Key × V}
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt⁻ : ∃ (λ i → BOBMap V [ proj₁ p ] u pred[ i ⊕ hr ]))
    (bal : hl ~ hr ⊔ h)
    → @erased [ proj₁ p ] <⁺ [ k ]
    → Any (_≡_ v) k (proj₂ rt⁻)
    → Any (_≡_ v) k (proj₂ (joinʳ⁻ p lt rt⁻ bal))
anyᴿ-joinᴿ⁻ {hr = 0} lt (i , rt) bal ord ()
anyᴿ-joinᴿ⁻ {hr = suc _} lt (1# , rt) bal ord prf = right ⦃ ord ⦄ prf
anyᴿ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~+ ord prf = right ⦃ ord ⦄ prf
anyᴿ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~0 ord prf = right ⦃ ord ⦄ prf
anyᴿ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~- ord prf = anyᴿjoinᴸ⁺ (1# , lt) rt ~- ord prf

anyᴸ-joinᴸ⁻ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k : Key}
    {v : V}
    {p : Key × V}
    (lt⁻ : ∃ (λ i → BOBMap V l [ proj₁ p ] pred[ i ⊕ hl ]))
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → @erased [ k ] <⁺ [ proj₁ p ]
    → Any (_≡_ v) k (proj₂ lt⁻)
    → Any (_≡_ v) k (proj₂ (joinˡ⁻ p lt⁻ rt bal))
anyᴸ-joinᴸ⁻ {hl = 0} (i , lt) rt bal ord ()
anyᴸ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~+ ord prf = anyᴸjoinᴿ⁺ lt (1# , rt) ~+ ord prf
anyᴸ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~0 ord prf = left ⦃ ord ⦄ prf
anyᴸ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~- ord prf = left ⦃ ord ⦄ prf
anyᴸ-joinᴸ⁻ {hl = suc _} (1# , lt) rt bal ord prf = left ⦃ ord ⦄ prf

anyᴿ-joinᴸ⁻ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k : Key}
    {v : V}
    {p : Key × V}
    (lt⁻ : ∃ (λ i → BOBMap V l [ proj₁ p ] pred[ i ⊕ hl ]))
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → @erased [ proj₁ p ] <⁺ [ k ]
    → Any (_≡_ v) k rt
    → Any (_≡_ v) k (proj₂ (joinˡ⁻ p lt⁻ rt bal))
anyᴿ-joinᴸ⁻ {hl = 0} (0# , lt) rt bal ord prf = right ⦃ ord ⦄ prf
anyᴿ-joinᴸ⁻ {hl = 0} (1# , lt) rt bal ord prf = right ⦃ ord ⦄ prf
anyᴿ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~+ ord prf = anyᴿjoinᴿ⁺ lt (1# , rt) ~+ ord prf
anyᴿ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~0 ord prf = right ⦃ ord ⦄ prf
anyᴿ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~- ord prf = right ⦃ ord ⦄ prf
anyᴿ-joinᴸ⁻ {hl = suc _} (1# , lt) rt bal ord prf = right ⦃ ord ⦄ prf

anyᴸ-joinᴿ⁻ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k : Key}
    {v : V}
    {p : Key × V}
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt⁻ : ∃ (λ i → BOBMap V [ proj₁ p ] u pred[ i ⊕ hr ]))
    (bal : hl ~ hr ⊔ h)
    → @erased [ k ] <⁺ [ proj₁ p ]
    → Any (_≡_ v) k lt
    → Any (_≡_ v) k (proj₂ (joinʳ⁻ p lt rt⁻ bal))
anyᴸ-joinᴿ⁻ {hr = 0} lt (0# , rt) bal ord prf = left ⦃ ord ⦄ prf
anyᴸ-joinᴿ⁻ {hr = 0} lt (1# , rt) bal ord prf = left ⦃ ord ⦄ prf
anyᴸ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~+ ord prf = left ⦃ ord ⦄ prf
anyᴸ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~0 ord prf = left ⦃ ord ⦄ prf
anyᴸ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~- ord prf = anyᴸjoinᴸ⁺ (1# , lt) rt ~- ord prf
anyᴸ-joinᴿ⁻ {hr = suc _} lt (1# , rt) bal ord prf = left ⦃ ord ⦄ prf

herejoinᴸ⁻ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k : Key}
    {v : V}
    (lt⁻ : ∃ (λ i → BOBMap V l [ k ] pred[ i ⊕ hl ]))
    (rt : BOBMap V [ k ] u hr)
    (bal : hl ~ hr ⊔ h)
    → Any (_≡_ v) k (proj₂ (joinˡ⁻ (k , v) lt⁻ rt bal))
herejoinᴸ⁻ {hl = 0} (0# , lt) rt bal = here ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ refl
herejoinᴸ⁻ {hl = 0} (1# , lt) rt bal = here ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ refl
herejoinᴸ⁻ {hl = suc _} (0# , lt) rt ~+ = herejoinᴿ⁺ lt (1# , rt) ~+
herejoinᴸ⁻ {hl = suc _} (0# , lt) rt ~0 = here ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ refl
herejoinᴸ⁻ {hl = suc _} (0# , lt) rt ~- = here ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ refl
herejoinᴸ⁻ {hl = suc _} (1# , lt) rt bal = here ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ refl

herejoinᴿ⁻ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k : Key}
    {v : V}
    (lt : BOBMap V l [ k ] hl)
    (rt⁻ : ∃ (λ i → BOBMap V [ k ] u pred[ i ⊕ hr ]))
    (bal : hl ~ hr ⊔ h)
    → Any (_≡_ v) k (proj₂ (joinʳ⁻ (k , v) lt rt⁻ bal))
herejoinᴿ⁻ {hr = 0} lt (0# , rt) bal = here ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ refl
herejoinᴿ⁻ {hr = 0} lt (1# , rt) bal = here ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ refl
herejoinᴿ⁻ {hr = suc _} lt (0# , rt) ~+ = here ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ refl
herejoinᴿ⁻ {hr = suc _} lt (0# , rt) ~0 = here ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ refl
herejoinᴿ⁻ {hr = suc _} lt (0# , rt) ~- = herejoinᴸ⁺ (1# , lt) rt ~-
herejoinᴿ⁻ {hr = suc _} lt (1# , rt) bal = here ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ refl

anyRaise : ∀ {l y u : Key⁺} {h : ℕ}
          ⦃ @erased y<u : y <⁺ u ⦄
          {k : Key}
          {v : V}
          {m : BOBMap V l y h}
          → k ↦ v ∈ m
          → k ↦ v ∈ (raise m)
anyRaise {k = k} {m = leaf} ()
anyRaise ⦃ y<u = y<u ⦄ {k} {m = node p l r b} (here prf) = here ⦃ k≤u = trans⁺ [ k ] (mklim r) y<u ⦄ prf
anyRaise {k = k} {m = node p l r b} (left prf) = left prf
anyRaise {k = k} {m = node p l r b} (right prf) = right (anyRaise prf)

anyJoinᴸ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k kₚ : Key}
    {v : V}
    (lm : BOBMap V l [ kₚ ] hl)
    (rm : BOBMap V [ kₚ ] u hr)
    (bal : hl ~ hr ⊔ h)
    → Any (_≡_ v) k lm
    → @erased k < kₚ
    → Any (_≡_ v) k (proj₂ (join lm rm bal))
anyJoinᴸ lm (leaf ⦃ ord' ⦄) ~0 prf ord = anyRaise ⦃ ord' ⦄ prf
anyJoinᴸ lm (leaf ⦃ ord' ⦄) ~- prf ord = anyRaise ⦃ ord' ⦄ prf
anyJoinᴸ lm rm@(node _ _ _ _) bal prf ord with uncons rm
... | cons head l<u tail = prf'
  where
    lmR = (raise ⦃ l<u ⦄ lm)
    prf' = anyᴸ-joinᴿ⁻ {p = head } lmR tail bal [ trans ord [ l<u ]-lower ]ᴿ (anyRaise ⦃ l<u ⦄ prf)

anyUncons : ∀ {l u h} {k : Key} {v : V}
    {m : BOBMap V l u (suc h)}
    → k ↦ v ∈ m
    → k ↦ v ∈ proj₂ (Cons.tail $ uncons m) ⊎ (k , v) ≡ (Cons.head $ uncons m)
anyUncons {k = k} {m = node p leaf rm ~+} (here refl) = inj₂ refl
anyUncons {k = k} {m = node p leaf rm ~+} (right prf) = inj₁ prf
anyUncons {k = k} {m = node p leaf leaf ~0} (here refl) = inj₂ refl
anyUncons {k = k} {m = node p lm@(node _ _ _ _) rm bal} prf with uncons lm in pUncons
... | cons head l<u tail with prf
... | here refl = inj₁ (herejoinᴸ⁻ tail rm bal)
... | right ⦃ ord ⦄ x = inj₁ (anyᴿ-joinᴸ⁻ tail rm bal ord x)
... | left ⦃ ord ⦄ x with anyUncons x
... | inj₁ x rewrite pUncons = inj₁ (anyᴸ-joinᴸ⁻ tail rm bal ord x )
... | inj₂ y rewrite pUncons = inj₂ y

minHead : ∀ {l u h} {k : Key⁺}
  (m : BOBMap V l u (suc h))
  → @erased l <⁺ k
  → [  proj₁ (Cons.head $ uncons m) ] <⁺ k
minHead (node p leaf rm ~+) ord = {!!}
minHead (node p leaf leaf ~0) ord = {!!}
minHead (node p lm@(node _ _ _ _) rm bal) ord = {!!}

anyJoinᴿ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k kₚ : Key}
    {v : V}
    (lm : BOBMap V l [ kₚ ] hl)
    (rm : BOBMap V [ kₚ ] u hr)
    (bal : hl ~ hr ⊔ h)
    → Any (_≡_ v) k rm
    → @erased [ kₚ ] <⁺ [ k ]
    → Any (_≡_ v) k (proj₂ (join lm rm bal))
anyJoinᴿ lm leaf bal () ord
anyJoinᴿ {l} lm rm@(node _ _ _ _) bal prf ord with uncons rm in pUncons
... | cons head l<u (i , tail) with anyUncons prf
... | inj₂ refl rewrite pUncons = herejoinᴿ⁻ lmR (i , tail) bal
  where
    lmR = (raise ⦃ l<u ⦄ lm)
... | inj₁ prfᴿ with minHead rm ord
... | ord' rewrite pUncons = anyᴿ-joinᴿ⁻ (raise ⦃ l<u ⦄ lm) (i , tail) bal ord' prfᴿ

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

---------------------------------------------------------------------------------
-- del-∉
---------------------------------------------------------------------------------
postulate
  inᴿ-joinᴿ⁻ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k : Key}
    {v : V}
    {p : Key × V}
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt⁻ : ∃ (λ i → BOBMap V [ proj₁ p ] u pred[ i ⊕ hr ]))
    (bal : hl ~ hr ⊔ h)
    → @erased [ proj₁ p ] <⁺ [ k ]
    → Any (_≡_ v) k (proj₂ (joinʳ⁻ p lt rt⁻ bal))
    → Any (_≡_ v) k (proj₂ rt⁻)
  inᴸ-joinᴸ⁻ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k : Key}
    {v : V}
    {p : Key × V}
    (lt⁻ : ∃ (λ i → BOBMap V l [ proj₁ p ] pred[ i ⊕ hl ]))
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → @erased [ k ] <⁺ [ proj₁ p ]
    → Any (_≡_ v) k (proj₂ (joinˡ⁻ p lt⁻ rt bal))
    → Any (_≡_ v) k (proj₂ lt⁻)
  inᴿ-joinᴸ⁻ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k : Key}
    {v : V}
    {p : Key × V}
    (lt⁻ : ∃ (λ i → BOBMap V l [ proj₁ p ] pred[ i ⊕ hl ]))
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → @erased [ proj₁ p ] <⁺ [ k ]
    → Any (_≡_ v) k (proj₂ (joinˡ⁻ p lt⁻ rt bal))
    → Any (_≡_ v) k rt
  inᴸ-joinᴿ⁻ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k : Key}
    {v : V}
    {p : Key × V}
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt⁻ : ∃ (λ i → BOBMap V [ proj₁ p ] u pred[ i ⊕ hr ]))
    (bal : hl ~ hr ⊔ h)
    → @erased [ k ] <⁺ [ proj₁ p ]
    → Any (_≡_ v) k (proj₂ (joinʳ⁻ p lt rt⁻ bal))
    → Any (_≡_ v) k lt
  inC-joinᴿ⁻ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {v : V}
    {p : Key × V}
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt⁻ : ∃ (λ i → BOBMap V [ proj₁ p ] u pred[ i ⊕ hr ]))
    (bal : hl ~ hr ⊔ h)
    → Any (_≡_ v) (proj₁ p) (proj₂ (joinʳ⁻ p lt rt⁻ bal))
    → v ≡ (proj₂ p)
  inC-joinᴸ⁻ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {v : V}
    {p : Key × V}
    (lt⁻ : ∃ (λ i → BOBMap V l [ proj₁ p ] pred[ i ⊕ hl ]))
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → Any (_≡_ v) (proj₁ p) (proj₂ (joinˡ⁻ p lt⁻ rt bal))
    → v ≡ (proj₂ p)

∉Left : ∀ {l u : Key⁺} {hl hr h : ℕ}
  {k k' : Key}
  {v : V}
  {lm : BOBMap V l [ k ] hl}
  {rm : BOBMap V [ k ] u hr}
  {b : hl ~ hr ⊔ h}
  → k' < k
  → k' ∉ (node (k , v) lm rm b)
  → k' ∉ lm
∉Left {k = k} {k'} {lm = lm} {rm} ord prf ∈lm with compare k' k
... | tri< a _ _ = prf (left ⦃ [ a ]ᴿ ⦄ ∈lm)
... | tri≈ _ refl _ = prf (here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ tt)
... | tri> a _ _ = a ord

∉Right : ∀ {l u : Key⁺} {hl hr h : ℕ}
  {k k' : Key}
  {v : V}
  {lm : BOBMap V l [ k ] hl}
  {rm : BOBMap V [ k ] u hr}
  {b : hl ~ hr ⊔ h}
  → k < k'
  → k' ∉ (node (k , v) lm rm b)
  → k' ∉ rm
∉Right {k = k} {k'} {lm = lm} {rm} ord prf ∈rm with compare k' k
... | tri< _ _ c = c ord
... | tri≈ _ refl _ = prf (here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ tt)
... | tri> _ _ c = prf (right ⦃ [ c ]ᴿ ⦄ ∈rm)

del-∉del⊆ : ∀ {l u : Key⁺} {h : ℕ} (k : Key)
        ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
        (m : BOBMap V l u h)
        → k ∉ m
        → proj₂ (delete k m) ⊆ m
del-∉del⊆ k leaf prf k' v ()
del-∉del⊆ k (node p lm rm bal) prf k' v prf' with compare k (proj₁ p)
... | tri≈ _ refl _ = ⊥-elim (prf (here tt))
del-∉del⊆ k (node p lm rm bal) prf k' v prf' | tri< k<p _ _ with compare k' (proj₁ p)
... | tri< k'<p _ _ = left ⦃ [ k'<p ]ᴿ ⦄ $ del-∉del⊆ k ⦃ k<u = [ k<p ]ᴿ ⦄ lm (∉Left k<p prf) k' v prfᴸ
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
... | tri> _ _ p<k' = right ⦃ [ p<k' ]ᴿ ⦄ $ del-∉del⊆ k ⦃ [ p<k ]ᴿ ⦄ rm (∉Right p<k prf) k' v prfᴿ
  where
    rm⁻ = delete k ⦃ [ p<k ]ᴿ ⦄ rm
    prfᴿ = inᴿ-joinᴿ⁻ lm rm⁻ bal [ p<k' ]ᴿ prf'

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
