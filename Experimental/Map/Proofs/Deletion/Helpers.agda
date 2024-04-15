{-# OPTIONS --erasure #-}
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet

module Map.Proofs.Deletion.Helpers {k ℓ₁ ℓ} (order : OrdSet k ℓ₁) (V : Set ℓ) where

open import Data.Nat.Base using (ℕ; suc)
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
