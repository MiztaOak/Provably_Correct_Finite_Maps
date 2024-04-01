{-# OPTIONS --erasure #-}
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet

module Map.Proofs.Proofs {k ℓ₁ ℓ} (order : OrdSet k ℓ₁) (V : Set ℓ) where

open import Level using (Level; _⊔_) renaming (suc to s; zero to z)
open import Data.Maybe.Base hiding (map)
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality hiding (trans; [_])
open import Data.Nat.Base using (ℕ; _*_; suc; zero)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Binary.Definitions
open import Relation.Binary.Construct.Add.Extrema.Strict using ([<]-injective)
open import Relation.Unary using (Pred)

open import Prelude
open import Map.BOBMap order as BOB
open StrictTotalOrder (toStrictTotalOrder order) renaming (Carrier to Key)

eqFromJust : ∀ {l : Level} {A : Set l} {a b : A} → just a ≡ just b → a ≡ b
eqFromJust refl = refl

_↦_∈_ : Key → V → {l u : Key⁺} {h : ℕ} → BOBMap V l u h → Set (k ⊔ ℓ₁ ⊔ ℓ)
k ↦ v ∈ m = Any (λ v' → v ≡ v') k m

_∈_ : Key → {l u : Key⁺} {h : ℕ} → BOBMap V l u h → Set (k ⊔ ℓ₁ ⊔ ℓ)
k ∈ m = Any {ℓₚ = z} (λ _ → True) k m

_∉_ : Key → {l u : Key⁺} {h : ℕ} → BOBMap V l u h → Set (k ⊔ ℓ₁ ⊔ ℓ)
k ∉ m = ¬ (k ∈ m)

_⊆_ : {l u : Key⁺} {h h' : ℕ} → BOBMap V l u h → BOBMap V l u h' → Set (k ⊔ ℓ₁ ⊔ ℓ)
n ⊆ m = ∀ k v → k ↦ v ∈ n → k ↦ v ∈ m

_≐_ : {l u : Key⁺} {h h' : ℕ} → BOBMap V l u h → BOBMap V l u h' → Set (k ⊔ ℓ₁ ⊔ ℓ)
n ≐ m = (n ⊆ m) × (m ⊆ n)

[_]-lower : ∀ {x y} → [ x ] <⁺ [ y ] → x < y
[ ord ]-lower = [<]-injective _<_ ord

irreflex : ∀ {k k'} → k < k' → ¬ (k ≡ k')
irreflex ord refl = irrefl refl ord

⊥-elim : ∀ {w} {Whatever : Set w} → @erased ⊥ → Whatever
⊥-elim ()

anyLeft : ∀ {l u : Key⁺} {hl hr h : ℕ} {(k , v) : Key × V}
          {lm : BOBMap V l [ k ] hl}
          {rm : BOBMap V [ k ] u hr}
          {b : hl ~ hr ⊔ h}
          {k' : Key}
          → k' < k
          → k' ∈ node (k , v) lm rm b
          → k' ∈ lm
anyLeft ord (here x) = ⊥-elim (irrefl refl ord)
anyLeft ord (left prf) = prf
anyLeft ord (right ⦃ ord' ⦄ prf) = ⊥-elim (asym ord [ ord' ]-lower)

anyRight : ∀ {l u : Key⁺} {hl hr h : ℕ} {(k , v) : Key × V}
           {lm : BOBMap V l [ k ] hl}
           {rm : BOBMap V [ k ] u hr}
           {b : hl ~ hr ⊔ h}
           {k' : Key}
           → k < k'
           → k' ∈ node (k , v) lm rm b
           → k' ∈ rm
anyRight ord (here x) = ⊥-elim (irrefl refl ord)
anyRight ord (left ⦃ ord' ⦄ prf) = ⊥-elim (asym ord [ ord' ]-lower)
anyRight ord (right prf) = prf

@erased anyMinOrd : ∀ {ℓₚ} {P : Pred V ℓₚ} {l u : Key⁺} {h : ℕ} {m : BOBMap V l u h} {k : Key}
  → Any P k m
  → l <⁺ [ k ]
anyMinOrd (here ⦃ l<k ⦄ x) = l<k
anyMinOrd (left ⦃ l<k ⦄ prf) = anyMinOrd prf
anyMinOrd {l = l} (right {lm = lm} ⦃ p<k ⦄ prf) = trans⁺ l (mklim lm) p<k

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

∈Contradiction : ∀ {l u : Key⁺} {h : ℕ} {m : BOBMap V l u h} {k k' : Key}
                 → k ∉ m
                 → k' ∈ m
                 → k ≢ k'
∈Contradiction {k = k} {k'} prf prf' with compare k k'
... | tri< _ ¬b _ = ¬b
... | tri≈ _ refl _ = ⊥-elim (prf prf')
... | tri> _ ¬b _ = ¬b

---------------------------------------------------------------------------------
-- Convert _↦_∈_ to _∈_
---------------------------------------------------------------------------------
↦∈To∈ : ∀ {l u : Key⁺} {h : ℕ} {k : Key} {v : V} {m : BOBMap V l u h}
          → k ↦ v ∈ m → k ∈ m
↦∈To∈ (here x) = here tt
↦∈To∈ (left prf) = left (↦∈To∈ prf)
↦∈To∈ (right prf) = right (↦∈To∈ prf)



{-
compareSelf : ∀ (k : Key) → compare k k ≡ tri≈ (irrefl refl) refl (irrefl refl)
compareSelf k with compare k k
... | tri≈ _ refl _ = {!!}
... | tri< a ¬b ¬c = contradiction refl ¬b
... | tri> ¬a ¬b c = contradiction refl ¬b

compareLeft : ∀ {k k' : Key} → (ord : k < k') → compare k k' ≡ tri< ord {!!} {!!}
compareLeft {k} {k'} ord with compare k k'
... | le a = {!!}
... | eq b = {!!}
... | ge c = {!!}


compareRight : ∀ {k k' : K} → (ord : # k' ≺Ex # k) → compare k k' ≡ inj₂ (inj₂ (! {{ord}}))
compareRight {k} {k'} ord with compare k k'
compareRight {k} {k'} ord
  | inj₁ (! ⦃ prf ⦄) with ≺Absurd ord prf
... | ()
compareRight {k} {k'} ord
  | eq with inreflex ord refl
... | ()
compareRight {k} {k'} ord
  | inj₂ (inj₂ (! ⦃ prf ⦄)) with ≺Eq ord prf
... | refl = refl
-}
