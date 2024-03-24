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
-- del-∉
---------------------------------------------------------------------------------
del-∉ : ∀ {l u : Key⁺} {h : ℕ} (k : Key)
        ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
        (m : BOBMap V l u h)
        → k ∉ m
        → proj₂ (delete k m) ≐ m
del-∉ k leaf prf = (λ _ _ x → x) , λ _ _ x → x -- should this be allowed?
del-∉ k (node p lm rm bal) prf with compare k (proj₁ p)
... | tri< a ¬b ¬c = {!!}
... | tri≈ ¬a refl ¬c = ⊥-elim (prf (here tt))
... | tri> ¬a ¬b c = (λ k' v x → {!!}) , λ k' v x → {!!}

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

postulate
  inᴸ-joinᴸ⁻ : ∀ {l u : Key⁺} {hl hr h}
              {k : Key}
              {p : Key × V}
              ⦃ @erased l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ @erased p<u : [ proj₁ p ] <⁺ u ⦄
              (lt⁻ : ∃ λ i → BOBMap V l [ proj₁ p ] pred[ i ⊕ hl ])
              (rt : BOBMap V [ proj₁ p ] u hr)
              (bal : hl ~ hr ⊔ h)
              → [ k ] <⁺ [ proj₁ p ]
              → k ∈ (proj₂ (joinˡ⁻ p lt⁻ rt bal))
              → k ∈ proj₂ lt⁻
  inᴿ-joinᴿ⁻ : ∀ {l u : Key⁺} {hl hr h}
              {k : Key}
              {p : Key × V}
              ⦃ @erased l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ @erased p<u : [ proj₁ p ] <⁺ u ⦄
              (lt : BOBMap V l [ proj₁ p ] hl)
              (rt⁻ : ∃ λ i → BOBMap V [ proj₁ p ] u pred[ i ⊕ hr ])
              (bal : hl ~ hr ⊔ h)
              → [ proj₁ p ] <⁺ [ k ]
              → k ∈ (proj₂ (joinʳ⁻ p lt rt⁻ bal))
              → k ∈ proj₂ rt⁻
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

del-∈ : ∀ {l u : Key⁺} {h : ℕ}
        (k : Key) (m : BOBMap V l u h)
        ⦃ l<k : l <⁺ [ k ] ⦄ ⦃ k<u : [ k ] <⁺ u ⦄
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
