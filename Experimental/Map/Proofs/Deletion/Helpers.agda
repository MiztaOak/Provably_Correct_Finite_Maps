{-# OPTIONS --erasure #-}
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet

module Map.Proofs.Deletion.Helpers {k ℓ₁ ℓ} (order : OrdSet k ℓ₁) (V : Set ℓ) where

open import Data.Nat.Base using (ℕ; suc; zero)
open import Data.Product using (_×_; ∃; proj₁; proj₂; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality hiding (trans; [_])
open import Relation.Binary.Definitions
open import Relation.Unary using (Pred)
open import Function.Base using (_$_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Prelude
open import Map.BOBMap order as BOB
open import Map.Proofs.Proofs order V
open StrictTotalOrder (toStrictTotalOrder order) renaming (Carrier to Key)
open import Map.Proofs.Insertion.Helpers order V

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

inMapsRaise' : ∀ {l y u : Key⁺} {h : ℕ}
          ⦃ @erased y<u : y <⁺ u ⦄
          {k : Key}
          {v : V}
          {m : BOBMap V l y h}
          → k ↦ v ∈ (raise m)
          → k ↦ v ∈ m
inMapsRaise' {k = k} {m = leaf} ()
inMapsRaise' {k = k} {m = node p l r b} (here refl) = here ⦃ k≤u = mklim r ⦄ refl
inMapsRaise' {k = k} {m = node p l r b} (left prf) = left prf
inMapsRaise' {k = k} {m = node p l r b} (right prf) = right (inMapsRaise' prf)


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
... | inj₁ prfᴿ rewrite pUncons = anyᴿ-joinᴿ⁻ (raise ⦃ l<u ⦄ lm) (i , tail) bal (anyMinOrd prfᴿ) prfᴿ

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
inᴿ-joinᴿ⁻ {hr = 0} lt (0# , rt) bal ord (here refl) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴿ-joinᴿ⁻ {hr = 0} lt (0# , rt) bal ord (left ⦃ ord' ⦄ _) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴿ⁻ {hr = 0} lt (1# , rt) bal ord (here refl) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴿ-joinᴿ⁻ {hr = 0} lt (1# , rt) bal ord (left ⦃ ord' ⦄ _) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~+ ord (here relf) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴿ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~+ ord (left ⦃ ord' ⦄ _) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~+ ord (right prf) = prf
inᴿ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~0 ord (here relf) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴿ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~0 ord (left ⦃ ord' ⦄ _) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~0 ord (right prf) = prf
inᴿ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~- ord prf = inᴿ-joinᴸ⁺ ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ (1# , lt) rt ~- ord prf
inᴿ-joinᴿ⁻ {hr = suc _} lt (1# , rt) bal ord (here relf) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴿ-joinᴿ⁻ {hr = suc _} lt (1# , rt) bal ord (left ⦃ ord' ⦄ _) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴿ⁻ {hr = suc _} lt (1# , rt) bal ord (right prf) = prf

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
inᴸ-joinᴿ⁻ {hr = 0} lt (0# , rt) bal ord (here refl) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴸ-joinᴿ⁻ {hr = 0} lt (0# , rt) bal ord (left prf) = prf
inᴸ-joinᴿ⁻ {hr = 0} lt (1# , rt) bal ord (here refl) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴸ-joinᴿ⁻ {hr = 0} lt (1# , rt) bal ord (left prf) = prf
inᴸ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~+ ord (here x) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴸ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~+ ord (left prf) = prf
inᴸ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~+ ord (right ⦃ ord' ⦄ _) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~0 ord (here x) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴸ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~0 ord (left prf) = prf
inᴸ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~0 ord (right ⦃ ord' ⦄ _) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~- ord prf = inᴸ-joinᴸ⁺ ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ (1# , lt) rt ~- ord prf
inᴸ-joinᴿ⁻ {hr = suc _} lt (1# , rt) bal ord (here x) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴸ-joinᴿ⁻ {hr = suc _} lt (1# , rt) bal ord (left prf) = prf
inᴸ-joinᴿ⁻ {hr = suc _} lt (1# , rt) bal ord (right ⦃ ord' ⦄ _) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)

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
inᴸ-joinᴸ⁻ {hl = 0} (0# , lt) rt bal ord (here x) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴸ-joinᴸ⁻ {hl = 0} (0# , lt) rt bal ord (right ⦃ ord' ⦄ prf) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴸ⁻ {hl = 0} (1# , lt) rt bal ord (here x) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴸ-joinᴸ⁻ {hl = 0} (1# , lt) rt bal ord (right ⦃ ord' ⦄ prf) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~+ ord prf = inᴸ-joinᴿ⁺ ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ lt (1# , rt) ~+ ord prf
inᴸ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~0 ord (here x) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴸ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~0 ord (left prf) = prf
inᴸ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~0 ord (right ⦃ ord' ⦄ prf) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~- ord (here x) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴸ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~- ord (left prf) = prf
inᴸ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~- ord (right ⦃ ord' ⦄ prf) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴸ⁻ {hl = suc _} (1# , lt) rt bal ord (here x) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴸ-joinᴸ⁻ {hl = suc _} (1# , lt) rt bal ord (left prf) = prf
inᴸ-joinᴸ⁻ {hl = suc _} (1# , lt) rt bal ord (right ⦃ ord' ⦄ prf) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)

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
inᴿ-joinᴸ⁻ {hl = 0} (0# , lt) rt bal ord (here x) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴿ-joinᴸ⁻ {hl = 0} (0# , lt) rt bal ord (right prf) = prf
inᴿ-joinᴸ⁻ {hl = 0} (1# , lt) rt bal ord (here x) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴿ-joinᴸ⁻ {hl = 0} (1# , lt) rt bal ord (right prf) = prf
inᴿ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~+ ord prf = inᴿ-joinᴿ⁺ ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ lt (1# , rt) ~+ ord prf
inᴿ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~0 ord (here x) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴿ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~0 ord (right prf) = prf
inᴿ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~0 ord (left ⦃ ord' ⦄ prf) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~- ord (here x) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴿ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~- ord (right prf) = prf
inᴿ-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~- ord (left ⦃ ord' ⦄ prf) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴸ⁻ {hl = suc _} (1# , lt) rt bal ord (here x) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴿ-joinᴸ⁻ {hl = suc _} (1# , lt) rt bal ord (right prf) = prf
inᴿ-joinᴸ⁻ {hl = suc _} (1# , lt) rt bal ord (left ⦃ ord' ⦄ prf) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)

inC-joinᴿ⁻ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {v : V}
    {p : Key × V}
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt⁻ : ∃ (λ i → BOBMap V [ proj₁ p ] u pred[ i ⊕ hr ]))
    (bal : hl ~ hr ⊔ h)
    → Any (_≡_ v) (proj₁ p) (proj₂ (joinʳ⁻ p lt rt⁻ bal))
    → v ≡ (proj₂ p)
inC-joinᴿ⁻ {hr = 0} lt (0# , rt) bal (here x) = x
inC-joinᴿ⁻ {hr = 0} lt (0# , rt) bal (left ⦃ ord ⦄ prf) = ⊥-elim (irrefl refl [ ord ]-lower)
inC-joinᴿ⁻ {hr = 0} lt (1# , rt) bal (here x) = x
inC-joinᴿ⁻ {hr = 0} lt (1# , rt) bal (left ⦃ ord ⦄ prf) = ⊥-elim (irrefl refl [ ord ]-lower)
inC-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~+ (here x) = x
inC-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~+ (left ⦃ ord ⦄ prf) = ⊥-elim (irrefl refl [ ord ]-lower)
inC-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~+ (right ⦃ ord ⦄ prf) = ⊥-elim (irrefl refl [ ord ]-lower)
inC-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~0 (here x) = x
inC-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~0 (left ⦃ ord ⦄ prf) = ⊥-elim (irrefl refl [ ord ]-lower)
inC-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~0 (right ⦃ ord ⦄ prf) = ⊥-elim (irrefl refl [ ord ]-lower)
inC-joinᴿ⁻ {hr = suc _} lt (0# , rt) ~- prf = inC-joinᴸ⁺ (1# , lt) rt ~- prf
inC-joinᴿ⁻ {hr = suc _} lt (1# , rt) bal (here x) = x
inC-joinᴿ⁻ {hr = suc _} lt (1# , rt) bal (left ⦃ ord ⦄ prf) = ⊥-elim (irrefl refl [ ord ]-lower)
inC-joinᴿ⁻ {hr = suc _} lt (1# , rt) bal (right ⦃ ord ⦄ prf) = ⊥-elim (irrefl refl [ ord ]-lower)

inC-joinᴸ⁻ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {v : V}
    {p : Key × V}
    (lt⁻ : ∃ (λ i → BOBMap V l [ proj₁ p ] pred[ i ⊕ hl ]))
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → Any (_≡_ v) (proj₁ p) (proj₂ (joinˡ⁻ p lt⁻ rt bal))
    → v ≡ (proj₂ p)
inC-joinᴸ⁻ {hl = 0} (0# , lt) rt bal (here x) = x
inC-joinᴸ⁻ {hl = 0} (0# , lt) rt bal (right ⦃ ord ⦄ prf) = ⊥-elim (irrefl refl [ ord ]-lower)
inC-joinᴸ⁻ {hl = 0} (1# , lt) rt bal (here x) = x
inC-joinᴸ⁻ {hl = 0} (1# , lt) rt bal (right ⦃ ord ⦄ prf) = ⊥-elim (irrefl refl [ ord ]-lower)
inC-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~0 (here x) = x
inC-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~0 (left ⦃ ord ⦄ prf) = ⊥-elim (irrefl refl [ ord ]-lower)
inC-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~0 (right ⦃ ord ⦄ prf) = ⊥-elim (irrefl refl [ ord ]-lower)
inC-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~- (here x) = x
inC-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~- (left ⦃ ord ⦄ prf) = ⊥-elim (irrefl refl [ ord ]-lower)
inC-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~- (right ⦃ ord ⦄ prf) = ⊥-elim (irrefl refl [ ord ]-lower)
inC-joinᴸ⁻ {hl = suc _} (0# , lt) rt ~+ prf = inC-joinᴿ⁺ lt (1# , rt) ~+ prf
inC-joinᴸ⁻ {hl = suc _} (1# , lt) rt bal (here x) = x
inC-joinᴸ⁻ {hl = suc _} (1# , lt) rt bal (left ⦃ ord ⦄ prf) = ⊥-elim (irrefl refl [ ord ]-lower)
inC-joinᴸ⁻ {hl = suc _} (1# , lt) rt bal (right ⦃ ord ⦄ prf) = ⊥-elim (irrefl refl [ ord ]-lower)

inJoinᴸ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k kₚ : Key}
    {v : V}
    (lm : BOBMap V l [ kₚ ] hl)
    (rm : BOBMap V [ kₚ ] u hr)
    (bal : hl ~ hr ⊔ h)
    → Any (_≡_ v) k (proj₂ (join lm rm bal))
    → @erased k < kₚ
    → Any (_≡_ v) k lm
inJoinᴸ {k = k} {kₚ} lm leaf ~0 prf ord = inMapsRaise' prf
inJoinᴸ {k = k} {kₚ} lm leaf ~- prf ord = inMapsRaise' prf
inJoinᴸ {k = k} {kₚ} lm rm@(node _ _ _ _) bal prf ord with uncons rm
... | cons head l<u tail =
  inMapsRaise' ⦃ l<u ⦄ (inᴸ-joinᴿ⁻ (raise ⦃ l<u ⦄ lm) tail bal [ trans ord [ l<u ]-lower ]ᴿ prf)

{-# TERMINATING #-}
-- trust me bro (but for real this needs to be fixxed)
inUncons : ∀ {l u h} {k : Key} {v : V}
    {m : BOBMap V l u (suc h)}
    → k ↦ v ∈ proj₂ (Cons.tail $ uncons m)
    → k ↦ v ∈ m
inUncons {m = node p leaf rm@(node _ _ _ _) ~+} prf = right ⦃ anyMinOrd prf ⦄ prf
inUncons {m = node p leaf leaf ~0} ()
inUncons {k = k} {m = node p lm@(node p' l r b) rm bal} prf with uncons lm in unConsEq
... | cons h ord t with compare k (proj₁ p)
... | eq refl rewrite inC-joinᴸ⁻ t rm bal prf = here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ refl
... | ge p<k = right ⦃ [ p<k ]ᴿ ⦄ (inᴿ-joinᴸ⁻ t rm bal [ p<k ]ᴿ prf)
... | le k<p with inᴸ-joinᴸ⁻ t rm bal [ k<p ]ᴿ prf
... | prf' with unConsEq
... | refl = left ⦃ anyMaxOrd prf' ⦄ (inUncons prf')

isHeadUncons : ∀ {l u h} {k : Key} {v : V}
    {m : BOBMap V l u (suc h)}
    → (k , v) ≡ (Cons.head $ uncons m)
    → k ↦ v ∈ m
isHeadUncons {m = node p leaf rm ~+} refl = here ⦃ k≤u = mklim rm ⦄ refl
isHeadUncons {m = node p leaf leaf ~0} refl = here refl
isHeadUncons {k = k} {m = node p lm@(node _ _ rm' _) rm bal} prf with isHeadUncons {m = lm} prf
... | prf = left ⦃ anyMaxOrd prf ⦄ prf

notInLeft' : ∀ {l : Key⁺} {h : ℕ} {k u : Key}
  → (m : BOBMap V l [ u ] h)
  → @erased u < k
  → k ∉ m
notInLeft' leaf ord ()
notInLeft' (node p lm rm bal) ord (here _) = ⊥-elim (asym ord [ mklim rm ]-lower)
notInLeft' (node p lm rm bal) ord (left ⦃ ord' ⦄ _) =
  ⊥-elim (asym ord (trans [ ord' ]-lower [ mklim rm ]-lower ))
notInLeft' (node p lm rm bal) ord (right prf) = notInLeft' rm ord prf

inJoinᴿ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k kₚ : Key}
    {v : V}
    (lm : BOBMap V l [ kₚ ] hl)
    (rm : BOBMap V [ kₚ ] u hr)
    (bal : hl ~ hr ⊔ h)
    → Any (_≡_ v) k (proj₂ (join lm rm bal))
    → @erased kₚ < k
    → Any (_≡_ v) k rm
inJoinᴿ lm leaf ~0 prf ord = ⊥-elim (notInLeft' lm ord (↦∈To∈ (inMapsRaise' prf)))
inJoinᴿ lm leaf ~- prf ord = ⊥-elim (notInLeft' lm ord (↦∈To∈ (inMapsRaise' prf)))
inJoinᴿ {k = k} lm rm@(node _ _ _ _) bal prf ord with uncons rm in eqUncons
... | cons head l<u tail with eqUncons
... | refl with compare k (proj₁ head)
... | le a = ⊥-elim (notInLeft' lm ord (↦∈To∈ prf'))
  where
    prf' = inMapsRaise' ⦃ l<u ⦄ (inᴸ-joinᴿ⁻ (raise ⦃ l<u ⦄ lm) tail bal [ a ]ᴿ prf)
... | eq refl rewrite inC-joinᴿ⁻ (raise ⦃ l<u ⦄ lm) tail bal prf = isHeadUncons refl
... | ge c with inᴿ-joinᴿ⁻ (raise ⦃ l<u ⦄ lm) tail bal [ c ]ᴿ prf
... | x = inUncons {m = rm} x

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

--- -}
--- -}
--- -}
