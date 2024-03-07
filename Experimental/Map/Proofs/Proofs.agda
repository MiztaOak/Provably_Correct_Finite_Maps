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

{-
  liftMap : ∀ {l u : Key⁺} {h : ℕ} → BOBMap V l u h → BOBMap V l ⊤⁺ h
  liftMap {l} {u} (leaf ⦃ l≤u ⦄) = leaf ⦃ {!maximum!} ⦄
  liftMap (node p lm rm bal) = node p lm (liftMap rm) bal

  lowerMap : ∀ {l u : Ext K} {h : ℕ} → BOBMap (l , u) h → BOBMap (⊥' , u) h
  lowerMap {l} {u} (leaf ⦃ l≤u ⦄) = leaf ⦃ minEx {l} {u} l≤u ⦄
  lowerMap (node p lm rm bal) = node p (lowerMap lm) rm bal
-}
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

compareSelf k with compare k k
compareSelf k
  | inj₁ (! ⦃ prf ⦄) with inreflex prf refl
  ... | ()
compareSelf k
  | eq = refl
compareSelf k
  | inj₂ (inj₂ (! ⦃ prf ⦄)) with inreflex prf refl
... | ()

compareLeft : ∀ {k k' : K} → (ord : # k ≺Ex # k') → compare k k' ≡ inj₁ (! {{ord}})
compareLeft {k} {k'} ord with compare k k'
compareLeft {k} {k'} ord
  | inj₁ (! ⦃ prf ⦄) with ≺Eq ord prf
... | refl = refl
compareLeft {k} {k'} ord
  | inj₂ (inj₂ (! ⦃ prf ⦄)) with ≺Absurd ord prf
... | ()
compareLeft {k} {k'} ord
  | eq with inreflex ord refl
... | ()

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
@erased mapOrd : ∀ {l u : Key⁺} {h : ℕ} → BOBMap V l u h → l <⁺ u
mapOrd (leaf ⦃ l≤u ⦄) = l≤u
mapOrd {l} (node p lm rm bal) = trans⁺ l (mapOrd lm) (mapOrd rm)

¬Sym : ∀ {ℓ : Level} {A : Set ℓ} {a b : A} → ¬ (a ≡ b) → ¬ (b ≡ a)
¬Sym nEq x = nEq (sym x)

{-
anyRotRᴸ : ∀ {l u : Ext K} {hr : ℕ} {kᴾ : K}
         {P : Pred V ℓₚ}
         → ((k , v) : K × V)
         → (lm : BOBMap (l , # k) (suc (suc hr)))
         → (rm : BOBMap (# k , u) hr)
         → Any P kᴾ lm
         → Any P kᴾ (proj₂ (rotR (k , v) lm rm))
anyRotRᴸ {u = u} {kᴾ = kᴾ} p (node .(_ , _) lmL rmL ~0) rm (here x) =
  here {{mapOrd lmL}} {{transEx {# kᴾ} {# (proj₁ p)} {u} (mapOrd rmL) (mapOrd rm)}} x
anyRotRᴸ p (node pL lmL rmL ~0) rm (left prf) = left prf
anyRotRᴸ p (node pL lmL rmL ~0) rm (right prf) = right (left {{{!!}}} prf)
anyRotRᴸ {u = u} {kᴾ = kᴾ} p (node .(_ , _) lmL rmL ~-) rm (here x) =
  here {{mapOrd lmL}} {{transEx {# kᴾ} {# (proj₁ p)} {u} (mapOrd rmL) (mapOrd rm)}} x
anyRotRᴸ p (node pL lmL rmL ~-) rm (left prf) = left prf
anyRotRᴸ p (node pL lmL rmL ~-) rm (right prf) = right (left {{{!!}}} prf)
anyRotRᴸ {u = u} {kᴾ = kᴾ} p (node pL lmL (node pL' lmL' rmL' b) ~+) rm (here x) =
  left ⦃ {!!} {- mapOrd lmL' -} ⦄ (here ⦃ mapOrd lmL ⦄ ⦃ mapOrd lmL' ⦄ x)
anyRotRᴸ {kᴾ = kᴾ} p (node pL lmL (node pL' lmL' rmL' b) ~+) rm (left ⦃ k≺k' ⦄ x) =
  left ⦃ transEx {# kᴾ} {# (proj₁ pL)} {# (proj₁ pL')} k≺k' {!!} {- (mapOrd lmL') -} ⦄ (left x)
anyRotRᴸ {l = l} {u} {kᴾ = kᴾ} p (node pL lmL (node pL' lmL' rmL' b) ~+) rm (right ⦃ k'≤k ⦄ (here x)) =
  here ⦃ l≤k ⦄ ⦃ k≤u ⦄ x
    where
      @erased l≤k : l ≺Ex # kᴾ
      l≤k = transEx {l} {# (proj₁ pL)} {# kᴾ} (mapOrd lmL) k'≤k
      @erased k≤u : # kᴾ ≺Ex u
      k≤u = transEx {# kᴾ} {# (proj₁ p)} {u} (mapOrd rmL') (mapOrd rm)
anyRotRᴸ p (node pL lmL (node pL' lmL' rmL' b) ~+) rm (right (left x)) = left (right x)
anyRotRᴸ p (node pL lmL (node pL' lmL' rmL' b) ~+) rm (right (right x)) = right (left ⦃ {!!} ⦄ x)

anyRotRᴿ : ∀ {l u : Ext K} {hr : ℕ} {kᴾ : K}
         {P : Pred V ℓₚ}
         → ((k , v) : K × V)
         → (lm : BOBMap (l , # k) (suc (suc hr)))
         → (rm : BOBMap (# k , u) hr)
         → Any P kᴾ rm
         → Any P kᴾ (proj₂ (rotR (k , v) lm rm))
anyRotRᴿ = {!!}

anyRotLᴿ : ∀ {l u : Ext K} {hl : ℕ} {kᴾ : K}
         {P : Pred V ℓₚ}
         → ((k , v) : K × V)
         → (lm : BOBMap (l , # k) hl)
         → (rm : BOBMap (# k , u) (suc (suc hl)))
         → Any P kᴾ rm
         → Any P kᴾ (proj₂ (rotL (k , v) lm rm))
anyRotLᴿ = {!!}

anyRotLᴸ : ∀ {l u : Ext K} {hl : ℕ} {kᴾ : K}
         {P : Pred V ℓₚ}
         → ((k , v) : K × V)
         → (lm : BOBMap (l , # k) hl)
         → (rm : BOBMap (# k , u) (suc (suc hl)))
         → Any P kᴾ lm
         → Any P kᴾ (proj₂ (rotL (k , v) lm rm))
anyRotLᴸ = {!!}
-}
