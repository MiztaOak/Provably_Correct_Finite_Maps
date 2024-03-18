{-# OPTIONS --erasure #-}
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet

module Map.Proofs.Proofs {k ℓ₁ ℓ} (order : OrdSet k ℓ₁) (V : Set ℓ) where

open import Level using (Level; _⊔_) renaming (suc to s; zero to z)
open import Data.Maybe.Base hiding (map)
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality hiding (trans; [_])
open import Data.Nat.Base using (ℕ; _*_; suc; zero)
open import Data.Empty
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Binary.Definitions
open import Relation.Binary.Construct.Add.Extrema.Strict using ([<]-injective)

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

⊥-elimErased : ∀ {w} {Whatever : Set w} → @erased ⊥ → Whatever
⊥-elimErased ()

{-
¬Left : ∀ {l u : Ext K} {hl hr h : ℕ} {P : Pred V ℓₚ} {k kₚ : K } {v : V}
          {lm : BOBMap (l , # k) hl} {rm : BOBMap (# k , u) hr}
          {bal : hl ~ hr ⊔ h}
          → ¬ (Any P kₚ (node (k , v) lm rm bal)) → ¬ (Any P kₚ lm)
¬Left prf lmP = prf (left {{{!!}}} lmP)

¬Right : ∀ {l u : Ext K} {hl hr h : ℕ} {P : Pred V ℓₚ} {k kₚ : K} {v : V}
           {lm : BOBMap (l , # k) hl} {rm : BOBMap (# k , u) hr}
           {bal : hl ~ hr ⊔ h}
           → ¬ (Any P kₚ (node (k , v) lm rm bal))
           → ¬ (Any P kₚ rm)
¬Right prf rmP = prf (right {{{!!}}} rmP)



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
