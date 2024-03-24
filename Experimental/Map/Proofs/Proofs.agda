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


---------------------------------------------------------------------------------
-- join left and right lemmas for insertion
---------------------------------------------------------------------------------
joinˡ⁺-lookup : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (k : Key)
    (p : Key × V)
    (lt⁺ : ∃ (λ i → BOBMap V l [ proj₁ p ] (i ⊕ hl)))
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → k < proj₁ p → lookup (proj₂ (joinˡ⁺ p lt⁺ rt bal)) k ≡ lookup (proj₂ lt⁺) k
joinˡ⁺-lookup k p (0# , lt) rt bal ord with compare k (proj₁ p)
... | tri≈ _ b _   = ⊥-elim (irrefl b ord)
... | tri> ¬a _ _  = ⊥-elim (¬a ord)
... | tri< a ¬b ¬c = refl
joinˡ⁺-lookup k p (1# , lt) rt ~0 ord with compare k (proj₁ p)
... | tri< a _ _  = refl
... | tri≈ _ b _  = ⊥-elim (irrefl b ord)
... | tri> ¬a _ _ = ⊥-elim (¬a ord)
joinˡ⁺-lookup k p (1# , lt) rt ~+ ord with compare k (proj₁ p)
... | tri< a _ _  = refl
... | tri≈ _ b _  = ⊥-elim (irrefl b ord)
... | tri> ¬a _ _ = ⊥-elim (¬a ord)
joinˡ⁺-lookup k p (1# , (node pᴸ ltᴸ rtᴸ ~0)) rt ~- ord with compare k (proj₁ pᴸ)
... | tri< a ¬b ¬c = refl
... | tri≈ _ refl _  = refl
... | tri> _ _ _ with compare k (proj₁ p)
... | tri< _ _ _ = refl
... | tri≈ ¬a refl ¬c = ⊥-elim (irrefl refl ord)
... | tri> ¬a _ _ = ⊥-elim (¬a ord)
joinˡ⁺-lookup k p (1# , (node pᴸ ltᴸ rtᴸ ~-)) rt ~- ord with compare k (proj₁ pᴸ)
... | tri< a ¬b ¬c = refl
... | tri≈ _ refl _  = refl
... | tri> _ _ _ with compare k (proj₁ p)
... | tri< _ _ _ = refl
... | tri≈ ¬a refl ¬c = ⊥-elim (irrefl refl ord)
... | tri> ¬a _ _ = ⊥-elim (¬a ord)
joinˡ⁺-lookup k p (1# , (node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ b) ~+)) rt ~- ord with compare k (proj₁ pᴿ) in cmpᴿ
... | tri< a ¬b ¬c with compare k (proj₁ pᴸ)
... | tri< a₁ ¬b₁ ¬c₁ = refl
... | tri≈ ¬a refl ¬c₁ = refl
... | tri> ¬a ¬b₁ c rewrite cmpᴿ = refl
joinˡ⁺-lookup k p (1# , (node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ b) ~+)) rt ~- ord
  | tri≈ _ refl _ with compare (proj₁ pᴿ) (proj₁ pᴸ)
... | tri< a ¬b ¬c = ⊥-elim (asym a [ mklim ltᴿ ]-lower)
... | tri≈ ¬a refl _ = ⊥-elim (¬a [ mklim ltᴿ ]-lower)
... | tri> _ _ _ rewrite cmpᴿ = refl
joinˡ⁺-lookup k p (1# , (node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ b) ~+)) rt ~- ord
  | tri> ¬k<R _ k>R with compare k (proj₁ p)
... | tri≈ ¬a refl ¬c = ⊥-elim (irrefl refl ord)
... | tri> ¬a _ _ = ⊥-elim (¬a ord)
... | tri< k<p _ _ with compare k (proj₁ pᴸ)
... | tri< k<L ¬b ¬c = ⊥-elim (¬k<R (trans k<L [ mklim ltᴿ ]-lower))
... | tri≈ _ refl _ = ⊥-elim (asym k>R [ mklim ltᴿ ]-lower)
... | tri> _ _ _ rewrite cmpᴿ = refl

joinʳ⁺-lookup : ∀ {l u : Key⁺} {hl hr h : ℕ}
  (k : Key)
  (p : Key × V)
  (lt : BOBMap V l [ proj₁ p ] hl)
  (rt⁺ : ∃ (λ i → BOBMap V [ proj₁ p ] u (i ⊕ hr)))
  (bal : hl ~ hr ⊔ h)
  → proj₁ p < k
  → lookup (proj₂ (joinʳ⁺ p lt rt⁺ bal)) k ≡ lookup (proj₂ rt⁺) k
joinʳ⁺-lookup k p lt (0# , rt) bal ord with compare k (proj₁ p)
... | tri< _ _ ¬c = ⊥-elim (¬c ord)
... | tri≈ _ _ ¬c = ⊥-elim (¬c ord)
... | tri> _ _ _  = refl
joinʳ⁺-lookup k p lt (1# , rt) ~0 ord with compare k (proj₁ p)
... | tri< _ _ ¬c = ⊥-elim (¬c ord)
... | tri≈ _ _ ¬c = ⊥-elim (¬c ord)
... | tri> _ _ _ = refl
joinʳ⁺-lookup k p lt (1# , rt) ~- ord with compare k (proj₁ p)
... | tri< _ _ ¬c = ⊥-elim (¬c ord)
... | tri≈ _ _ ¬c = ⊥-elim (¬c ord)
... | tri> _ _ _ = refl
joinʳ⁺-lookup k p lt (1# , (node pᴿ ltᴿ rtᴿ ~+)) ~+ ord with compare k (proj₁ pᴿ)
... | tri≈ _ refl _ = refl
... | tri> _ _ _ = refl
... | tri< _ _ _ with compare k (proj₁ p)
... | tri< _ _ ¬k<p = ⊥-elim (¬k<p ord)
... | tri≈ _ _ ¬k<p = ⊥-elim (¬k<p ord)
... | tri> _ _ _ = refl
joinʳ⁺-lookup k p lt (1# , (node pᴿ ltᴿ rtᴿ ~0)) ~+ ord with compare k (proj₁ pᴿ)
... | tri≈ _ refl _ = refl
... | tri> _ _ _ = refl
... | tri< _ _ _ with compare k (proj₁ p)
... | tri< _ _ ¬k<p = ⊥-elim (¬k<p ord)
... | tri≈ _ _ ¬k<p = ⊥-elim (¬k<p ord)
... | tri> _ _ _ = refl
joinʳ⁺-lookup k p lt (1# , (node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-)) ~+ ord with compare k (proj₁ pᴸ) in compL
... | tri< a _ ¬l<r with compare k (proj₁ p)
... | tri< _ _ ¬c = ⊥-elim (¬c ord)
... | tri≈ _ _ ¬c = ⊥-elim (¬c ord)
... | tri> _ _ _ with compare k (proj₁ pᴿ)
... | tri< _ _ _ rewrite compL = refl
... | tri≈ _ refl _ = ⊥-elim (¬l<r [ mklim rtᴸ ]-lower)
... | tri> ¬a _ _ = ⊥-elim (¬a (trans a [ mklim rtᴸ ]-lower))
joinʳ⁺-lookup k p lt (1# , (node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-)) ~+ ord
  | tri≈ _ refl _ with compare (proj₁ pᴸ) (proj₁ pᴿ)
... | tri< _ _ _ rewrite compL = refl
... | tri≈ _ refl _ = ⊥-elim (irrefl refl [ mklim rtᴸ ]-lower)
... | tri> ¬l<r _ _ = ⊥-elim (¬l<r [ mklim rtᴸ ]-lower)
joinʳ⁺-lookup k p lt (1# , (node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-)) ~+ ord
  | tri> _ _ _ with compare k (proj₁ pᴿ)
... | tri< _ _ _ rewrite compL = refl
... | tri≈ _ refl _ = refl
... | tri> _ _ _ = refl

anyᴸjoinᴸ⁺ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k : Key}
    {v : V}
    {p : Key × V}
    (lt⁺ : ∃ (λ i → BOBMap V l [ proj₁ p ] (i ⊕ hl)))
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → @erased [ k ] <⁺ [ proj₁ p ]
    → Any (_≡_ v) k (proj₂ lt⁺)
    → Any (_≡_ v) k (proj₂ (joinˡ⁺ p lt⁺ rt bal))
anyᴸjoinᴸ⁺ (0# , lt) rt bal ord prf = left ⦃ ord ⦄ prf
anyᴸjoinᴸ⁺ (1# , lt) rt ~+ ord prf = left ⦃ ord ⦄ prf
anyᴸjoinᴸ⁺ (1# , lt) rt ~0 ord prf = left ⦃ ord ⦄ prf
anyᴸjoinᴸ⁺ {k = k} (1# , (node pᴸ ltᴸ rtᴸ ~-)) rt ~- ord (here ⦃ o₁ ⦄ ⦃ o₂ ⦄ refl) =
  here ⦃ o₁ ⦄ ⦃ trans⁺ [ k ] o₂ (mklim rt)  ⦄ refl
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ rtᴸ ~-)) rt ~- ord (left prf) = left prf
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ rtᴸ ~-)) rt ~- ord (right prf) = right (left ⦃ ord ⦄ prf)
anyᴸjoinᴸ⁺ {k = k} (1# , (node pᴸ ltᴸ rtᴸ ~0)) rt ~- ord (here ⦃ o₁ ⦄ refl) =
  here ⦃ o₁ ⦄ ⦃ trans⁺ [ k ] ord (mklim rt) ⦄ refl
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ rtᴸ ~0)) rt ~- ord (left prf) = left prf
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ rtᴸ ~0)) rt ~- ord (right prf) = right (left ⦃ ord ⦄ prf)
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ b) ~+)) rt ~- ord (here ⦃ o₁ ⦄ refl) =
  left ⦃ mklim ltᴿ ⦄ (here ⦃ o₁ ⦄ ⦃ mklim ltᴿ ⦄ refl)
anyᴸjoinᴸ⁺ {k = k} (1# , (node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ b) ~+)) rt ~- ord (left ⦃ o ⦄ prf) =
  left ⦃ trans⁺ [ k ] o (mklim ltᴿ) ⦄ (left prf)
anyᴸjoinᴸ⁺ {l} {k = k} (1# , (node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ b) ~+)) rt ~- ord (right (here ⦃ l≤k ⦄ refl)) =
  here ⦃ trans⁺ l (mklim ltᴸ) l≤k ⦄ ⦃ trans⁺ [ k ] ord (mklim rt) ⦄ refl
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ b) ~+)) rt ~- ord (right (left prf)) = left (right prf)
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ b) ~+)) rt ~- ord (right (right prf)) = right (left ⦃ ord ⦄ prf)

anyᴿjoinᴿ⁺ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k : Key}
    {v : V}
    {p : Key × V}
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt⁺ : ∃ (λ i → BOBMap V [ proj₁ p ] u (i ⊕ hr)))
    (bal : hl ~ hr ⊔ h)
    → @erased [ proj₁ p ] <⁺ [ k ]
    → Any (_≡_ v) k (proj₂ rt⁺)
    → Any (_≡_ v) k (proj₂ (joinʳ⁺ p lt rt⁺ bal))
anyᴿjoinᴿ⁺ lt (0# , rt) bal ord prf = right ⦃ ord ⦄ prf
anyᴿjoinᴿ⁺ lt (1# , rt) ~0 ord prf = right ⦃ ord ⦄ prf
anyᴿjoinᴿ⁺ lt (1# , rt) ~- ord prf = right ⦃ ord ⦄ prf
anyᴿjoinᴿ⁺ {l} lt (1# , (node pᴿ ltᴿ rtᴿ ~+)) ~+ ord (here ⦃ k≤u = o ⦄ refl) =
  here ⦃ trans⁺ l (mklim lt) ord ⦄ ⦃ o ⦄ refl
anyᴿjoinᴿ⁺ lt (1# , (node pᴿ ltᴿ rtᴿ ~+)) ~+ ord (left prf) = left (right ⦃ ord ⦄ prf)
anyᴿjoinᴿ⁺ lt (1# , (node pᴿ ltᴿ rtᴿ ~+)) ~+ ord (right prf) = right prf
anyᴿjoinᴿ⁺ {l} lt (1# , (node pᴿ ltᴿ rtᴿ ~0)) ~+ ord (here ⦃ k≤u = o ⦄ refl) =
  here ⦃ trans⁺ l (mklim lt) ord ⦄ ⦃ o ⦄ refl
anyᴿjoinᴿ⁺ lt (1# , (node pᴿ ltᴿ rtᴿ ~0)) ~+ ord (left prf) = left (right ⦃ ord ⦄ prf)
anyᴿjoinᴿ⁺ lt (1# , (node pᴿ ltᴿ rtᴿ ~0)) ~+ ord (right prf) = right prf
anyᴿjoinᴿ⁺ lt (1# , (node pᴿ (node pᴸ ltᴸ rtᴸ b) rtᴿ ~-)) ~+ ord (here ⦃ k≤u = o₂ ⦄ refl) =
  right ⦃ mklim rtᴸ ⦄ (here ⦃ mklim rtᴸ ⦄ ⦃ o₂ ⦄ refl)
anyᴿjoinᴿ⁺ lt (1# , (node pᴿ (node pᴸ ltᴸ rtᴸ b) rtᴿ ~-)) ~+ ord (right ⦃ o ⦄ prf) =
  right ⦃ trans⁺ [ proj₁ pᴸ ] (mklim rtᴸ) o ⦄ (right prf)
anyᴿjoinᴿ⁺ {l} {k = k} lt (1# , (node pᴿ (node pᴸ ltᴸ rtᴸ b) rtᴿ ~-)) ~+ ord (left (here refl)) =
  here ⦃ trans⁺ l (mklim lt) ord ⦄ ⦃ trans⁺ [ k ] (mklim rtᴸ) (mklim rtᴿ) ⦄ refl
anyᴿjoinᴿ⁺ lt (1# , (node pᴿ (node pᴸ ltᴸ rtᴸ b) rtᴿ ~-)) ~+ ord (left (left prf)) =
  left (right ⦃ ord ⦄ prf)
anyᴿjoinᴿ⁺ lt (1# , (node pᴿ (node pᴸ ltᴸ rtᴸ b) rtᴿ ~-)) ~+ ord (left (right prf)) = right (left prf)

anyᴿjoinᴸ⁺ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k : Key}
    {v : V}
    {p : Key × V}
    (lt⁺ : ∃ (λ i → BOBMap V l [ proj₁ p ] (i ⊕ hl)))
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → @erased [ proj₁ p ] <⁺ [ k ]
    → Any (_≡_ v) k rt
    → Any (_≡_ v) k (proj₂ (joinˡ⁺ p lt⁺ rt bal))
anyᴿjoinᴸ⁺ (0# , lt) rt b ord prf = right ⦃ ord ⦄ prf
anyᴿjoinᴸ⁺ (1# , lt) rt ~+ ord prf = right ⦃ ord ⦄ prf
anyᴿjoinᴸ⁺ (1# , lt) rt ~0 ord prf = right ⦃ ord ⦄ prf
anyᴿjoinᴸ⁺ (1# , (node pᴸ ltᴸ rtᴸ ~-)) rt ~- ord prf =
  right ⦃ trans⁺ [ proj₁ pᴸ ] (mklim rtᴸ) ord ⦄ (right ⦃ ord ⦄ prf)
anyᴿjoinᴸ⁺ (1# , (node pᴸ ltᴸ rtᴸ ~0)) rt ~- ord prf =
  right ⦃ trans⁺ [ proj₁ pᴸ ] (mklim rtᴸ) ord ⦄ (right ⦃ ord ⦄ prf)
anyᴿjoinᴸ⁺ (1# , (node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ _) ~+)) rt ~- ord prf =
  right ⦃ trans⁺ [ proj₁ pᴿ ] (mklim rtᴿ) ord ⦄ (right ⦃ ord ⦄ prf)

anyᴸjoinᴿ⁺ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k : Key}
    {v : V}
    {p : Key × V}
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt⁺ : ∃ (λ i → BOBMap V [ proj₁ p ] u (i ⊕ hr)))
    (bal : hl ~ hr ⊔ h)
    → @erased [ k ] <⁺ [ proj₁ p ]
    → Any (_≡_ v) k lt
    → Any (_≡_ v) k (proj₂ (joinʳ⁺ p lt rt⁺ bal))
anyᴸjoinᴿ⁺ lt (0# , rt) b ord prf = left ⦃ ord ⦄ prf
anyᴸjoinᴿ⁺ lt (1# , rt) ~0 ord prf = left ⦃ ord ⦄ prf
anyᴸjoinᴿ⁺ lt (1# , rt) ~- ord prf = left ⦃ ord ⦄ prf
anyᴸjoinᴿ⁺ {k = k} lt (1# , (node pᴸ ltᴸ rtᴸ ~+)) ~+ ord prf =
  left ⦃ trans⁺ [ k ] ord (mklim ltᴸ) ⦄ (left ⦃ ord ⦄ prf)
anyᴸjoinᴿ⁺ {k = k} lt (1# , (node pᴸ ltᴸ rtᴸ ~0)) ~+ ord prf =
  left ⦃ trans⁺ [ k ] ord (mklim ltᴸ) ⦄ (left ⦃ ord ⦄ prf)
anyᴸjoinᴿ⁺ {k = k} lt (1# , (node pᴸ (node pᴿ lm _ _)  rtᴸ ~-)) ~+ ord prf =
  left ⦃ trans⁺ [ k ] ord (mklim lm) ⦄ (left ⦃ ord ⦄ prf)

herejoinᴸ⁺ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k : Key}
    {v : V}
    (lt⁺ : ∃ (λ i → BOBMap V l [ k ] (i ⊕ hl)))
    (rt : BOBMap V [ k ] u hr)
    (bal : hl ~ hr ⊔ h)
    → Any (_≡_ v) k (proj₂ (joinˡ⁺ (k , v) lt⁺ rt bal))
herejoinᴸ⁺ (0# , lm) rm bal = here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ refl
herejoinᴸ⁺ (1# , lm) rm ~+ = here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ refl
herejoinᴸ⁺ (1# , lm) rm ~0 = here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ refl
herejoinᴸ⁺ (1# , (node pᴸ ltᴸ rtᴸ ~-)) rm ~- = right ⦃ mklim rtᴸ ⦄ (here ⦃ mklim rtᴸ ⦄ ⦃ mklim rm ⦄ refl)
herejoinᴸ⁺ (1# , (node pᴸ ltᴸ rtᴸ ~0)) rm ~- = right ⦃ mklim rtᴸ ⦄ (here ⦃ mklim rtᴸ ⦄ ⦃ mklim rm ⦄ refl)
herejoinᴸ⁺ (1# , (node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ _) ~+)) rm ~- =
  right ⦃ mklim rtᴿ ⦄ (here ⦃ mklim rtᴿ ⦄ ⦃ mklim rm ⦄ refl)

herejoinᴿ⁺ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k : Key}
    {v : V}
    (lt : BOBMap V l [ k ] hl)
    (rt⁺ : ∃ (λ i → BOBMap V [ k ] u (i ⊕ hr)))
    (bal : hl ~ hr ⊔ h)
    → Any (_≡_ v) k (proj₂ (joinʳ⁺ (k , v) lt rt⁺ bal))
herejoinᴿ⁺ lm (0# , rm) bal = here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ refl
herejoinᴿ⁺ lm (1# , rm) ~- = here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ refl
herejoinᴿ⁺ lm (1# , rm) ~0 = here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ refl
herejoinᴿ⁺ lm (1# , (node pᴿ ltᴿ rtᴿ ~+)) ~+ = left ⦃ mklim ltᴿ ⦄ (here ⦃ mklim lm ⦄ ⦃ mklim ltᴿ ⦄ refl)
herejoinᴿ⁺ lm (1# , (node pᴿ ltᴿ rtᴿ ~0)) ~+ = left ⦃ mklim ltᴿ ⦄ (here ⦃ mklim lm ⦄ ⦃ mklim ltᴿ ⦄ refl)
herejoinᴿ⁺ lm (1# , (node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-)) ~+ =
  left ⦃ mklim ltᴸ ⦄ (here ⦃ mklim lm ⦄ ⦃ mklim ltᴸ ⦄ refl)

inᴸ-joinᴿ⁺ : ∀ {l u : Key⁺} {hl hr h : ℕ}
              (x : Key)
              (p : Key × V)
              ⦃ @erased l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ @erased p<u : [ proj₁ p ] <⁺ u ⦄
              (lt : BOBMap V l [ proj₁ p ] hl)
              (rt⁺ : ∃ λ i → BOBMap V [ proj₁ p ] u (i ⊕ hr))
              → (bal : hl ~ hr ⊔ h)
              → [ x ] <⁺ [ proj₁ p ]
              → x ∈ (proj₂ (joinʳ⁺ p lt rt⁺ bal))
              → x ∈ lt
inᴸ-joinᴿ⁺ x .(x , _) lt (0# , rt) bal ord (here tt) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴸ-joinᴿ⁺ x p lt (0# , rt) bal ord (left prf) = prf
inᴸ-joinᴿ⁺ x p lt (0# , rt) bal ord (right ⦃ ord' ⦄ prf) = ⊥-elim(asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴿ⁺ x p lt (1# , rt) ~- ord (here tt) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴸ-joinᴿ⁺ x p lt (1# , rt) ~- ord (left prf) = prf
inᴸ-joinᴿ⁺ x p lt (1# , rt) ~- ord (right ⦃ ord' ⦄ prf) = ⊥-elim(asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴿ⁺ x p lt (1# , rt) ~0 ord (here tt) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴸ-joinᴿ⁺ x p lt (1# , rt) ~0 ord (left prf) = prf
inᴸ-joinᴿ⁺ x p lt (1# , rt) ~0 ord (right ⦃ ord' ⦄ prf) = ⊥-elim(asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴿ⁺ x p lt (1# , (node pᴿ ltᴿ rtᴿ ~+)) ~+ ord (here tt) =
  ⊥-elim (asym [ ord ]-lower [ mklim ltᴿ ]-lower)
inᴸ-joinᴿ⁺ x p lt (1# , (node pᴿ ltᴿ rtᴿ ~+)) ~+ ord (left (here tt)) =
  ⊥-elim (irrefl⁺ [ x ] ord)
inᴸ-joinᴿ⁺ x p lt (1# , (node pᴿ ltᴿ rtᴿ ~+)) ~+ ord (left (left prf)) = prf
inᴸ-joinᴿ⁺ x p lt (1# , (node pᴿ ltᴿ rtᴿ ~+)) ~+ ord (left (right ⦃ ord' ⦄ prf)) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴿ⁺ x p lt (1# , (node pᴿ ltᴿ rtᴿ ~+)) ~+ ord (right ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ trans⁺ [ proj₁ p ] (mklim ltᴿ) ord' ]-lower)
inᴸ-joinᴿ⁺ x p lt (1# , (node pᴿ ltᴿ rtᴿ ~0)) ~+ ord (here tt) =
  ⊥-elim (asym [ ord ]-lower [ mklim ltᴿ ]-lower)
inᴸ-joinᴿ⁺ x p lt (1# , (node pᴿ ltᴿ rtᴿ ~0)) ~+ ord (left (here tt)) =
  ⊥-elim (irrefl⁺ [ x ] ord)
inᴸ-joinᴿ⁺ x p lt (1# , (node pᴿ ltᴿ rtᴿ ~0)) ~+ ord (left (left prf)) = prf
inᴸ-joinᴿ⁺ x p lt (1# , (node pᴿ ltᴿ rtᴿ ~0)) ~+ ord (left (right ⦃ ord' ⦄ prf)) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴿ⁺ x p lt (1# , (node pᴿ ltᴿ rtᴿ ~0)) ~+ ord (right ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ trans⁺ [ proj₁ p ] (mklim ltᴿ) ord' ]-lower)
inᴸ-joinᴿ⁺ x p lt (1# , (node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-)) ~+ ord (here tt) =
  ⊥-elim (asym [ ord ]-lower [ mklim ltᴸ ]-lower)
inᴸ-joinᴿ⁺ x p lt (1# , (node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-)) ~+ ord (right (here tt)) =
  ⊥-elim (asym [ ord ]-lower [ trans⁺ [ proj₁ p ] (mklim ltᴸ) (mklim rtᴸ) ]-lower)
inᴸ-joinᴿ⁺ x p lt (1# , (node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-)) ~+ ord (right ⦃ ord' ⦄ (left prf)) =
  ⊥-elim (asym [ ord ]-lower [ trans⁺ [ proj₁ p ] (mklim ltᴸ) ord' ]-lower)
inᴸ-joinᴿ⁺ x p lt (1# , (node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-)) ~+ ord (right ⦃ ord' ⦄ (right prf)) =
  ⊥-elim (asym [ ord ]-lower [ trans⁺ [ proj₁ p ] (mklim ltᴸ) ord' ]-lower)
inᴸ-joinᴿ⁺ x p lt (1# , (node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-)) ~+ ord (left (here tt)) =
  ⊥-elim (irrefl⁺ [ x ] ord)
inᴸ-joinᴿ⁺ x p lt (1# , (node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-)) ~+ ord (left (left prf)) = prf
inᴸ-joinᴿ⁺ x p lt (1# , (node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-)) ~+ ord (left (right ⦃ ord' ⦄ prf)) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)

inᴿ-joinᴸ⁺ : ∀ {l u : Key⁺} {hl hr h : ℕ}
              (x : Key)
              (p : Key × V)
              ⦃ @erased l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ @erased p<u : [ proj₁ p ] <⁺ u ⦄
              (lt⁺ : ∃ λ i → BOBMap V l [ proj₁ p ] (i ⊕ hl))
              (rt : BOBMap V [ proj₁ p ] u hr)
              → (bal : hl ~ hr ⊔ h)
              → [ proj₁ p ] <⁺ [ x ]
              → x ∈ (proj₂ (joinˡ⁺ p lt⁺ rt bal))
              → x ∈ rt
inᴿ-joinᴸ⁺ x .(x , _) (0# , lt) rt bal ord (here tt) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴿ-joinᴸ⁺ x p (0# , lt) rt bal ord (right prf) = prf
inᴿ-joinᴸ⁺ x p (0# , lt) rt bal ord (left ⦃ ord' ⦄ prf) = ⊥-elim(asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴸ⁺ x p (1# , lt) rt ~+ ord (here tt) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴿ-joinᴸ⁺ x p (1# , lt) rt ~+ ord (right prf) = prf
inᴿ-joinᴸ⁺ x p (1# , lt) rt ~+ ord (left ⦃ ord' ⦄ prf) = ⊥-elim(asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴸ⁺ x p (1# , lt) rt ~0 ord (here tt) = ⊥-elim (irrefl refl [ ord ]-lower)
inᴿ-joinᴸ⁺ x p (1# , lt) rt ~0 ord (right prf) = prf
inᴿ-joinᴸ⁺ x p (1# , lt) rt ~0 ord (left ⦃ ord' ⦄ prf) = ⊥-elim(asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴸ⁺ x p (1# , (node pᴿ ltᴿ rtᴿ ~-)) rt ~- ord (here tt) =
  ⊥-elim (asym [ ord ]-lower [ mklim rtᴿ ]-lower)
inᴿ-joinᴸ⁺ x p (1# , (node pᴿ ltᴿ rtᴿ ~-)) rt ~- ord (right (here tt)) =
  ⊥-elim (irrefl⁺ [ x ] ord)
inᴿ-joinᴸ⁺ x p (1# , (node pᴿ ltᴿ rtᴿ ~-)) rt ~- ord (right (right prf)) = prf
inᴿ-joinᴸ⁺ x p (1# , (node pᴿ ltᴿ rtᴿ ~-)) rt ~- ord (right (left ⦃ ord' ⦄ prf)) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴸ⁺ x p (1# , (node pᴿ ltᴿ rtᴿ ~-)) rt ~- ord (left ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [  trans⁺ [ x ] ord' (mklim rtᴿ)  ]-lower)
inᴿ-joinᴸ⁺ x p (1# , (node pᴿ ltᴿ rtᴿ ~0)) rt ~- ord (here tt) =
  ⊥-elim (asym [ ord ]-lower [ mklim rtᴿ ]-lower)
inᴿ-joinᴸ⁺ x p (1# , (node pᴿ ltᴿ rtᴿ ~0)) rt ~- ord (right (here tt)) =
  ⊥-elim (irrefl⁺ [ x ] ord)
inᴿ-joinᴸ⁺ x p (1# , (node pᴿ ltᴿ rtᴿ ~0)) rt ~- ord (right (right prf)) = prf
inᴿ-joinᴸ⁺ x p (1# , (node pᴿ ltᴿ rtᴿ ~0)) rt ~- ord (right (left ⦃ ord' ⦄ prf)) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴸ⁺ x p (1# , (node pᴿ ltᴿ rtᴿ ~0)) rt ~- ord (left ⦃ ord' ⦄ prf) =
  ⊥-elim (asym [ ord ]-lower [ trans⁺ [ x ] ord' (mklim rtᴿ) ]-lower)
inᴿ-joinᴸ⁺ x p (1# , (node pᴿ lt (node pᴸ ltᴸ rtᴸ _) ~+)) rt ~- ord (here tt) =
  ⊥-elim (asym [ ord ]-lower [ mklim rtᴸ ]-lower)
inᴿ-joinᴸ⁺ x p (1# , (node pᴿ lt (node pᴸ ltᴸ rtᴸ _) ~+)) rt ~- ord (left (here tt)) =
  ⊥-elim (asym [ ord ]-lower [  trans⁺ [ x ] (mklim ltᴸ) (mklim rtᴸ)  ]-lower)
inᴿ-joinᴸ⁺ x p (1# , (node pᴿ lt (node pᴸ ltᴸ rtᴸ _) ~+)) rt ~- ord (left ⦃ ord' ⦄ (right prf)) =
  ⊥-elim (asym [ ord ]-lower [ trans⁺ [ x ] ord' (mklim rtᴸ) ]-lower)
inᴿ-joinᴸ⁺ x p (1# , (node pᴿ lt (node pᴸ ltᴸ rtᴸ _) ~+)) rt ~- ord (left ⦃ ord' ⦄ (left prf)) =
  ⊥-elim (asym [ ord ]-lower [ trans⁺ [ x ] ord' (mklim rtᴸ) ]-lower)
inᴿ-joinᴸ⁺ x p (1# , (node pᴿ lt (node pᴸ ltᴸ rtᴸ _) ~+)) rt ~- ord (right (here tt)) =
  ⊥-elim (irrefl⁺ [ x ] ord)
inᴿ-joinᴸ⁺ x p (1# , (node pᴿ lt (node pᴸ ltᴸ rtᴸ _) ~+)) rt ~- ord (right (right prf)) = prf
inᴿ-joinᴸ⁺ x p (1# , (node pᴿ lt (node pᴸ ltᴸ rtᴸ _) ~+)) rt ~- ord (right (left ⦃ ord' ⦄ prf)) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)

inᴿ-joinᴿ⁺ : ∀ {l u : Key⁺} {hl hr h : ℕ}
              (x : Key)
              (p : Key × V)
              ⦃ @erased l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ @erased p<u : [ proj₁ p ] <⁺ u ⦄
              (lt : BOBMap V l [ proj₁ p ] hl)
              (rt⁺ : ∃ λ i → BOBMap V [ proj₁ p ] u (i ⊕ hr))
              (bal : hl ~ hr ⊔ h)
              → [ proj₁ p ] <⁺ [ x ]
              → x ∈ (proj₂ (joinʳ⁺ p lt rt⁺ bal))
              → x ∈ proj₂ rt⁺
inᴿ-joinᴿ⁺ x p lt (0# , rt) bal ord (here tt) = ⊥-elim (irrefl⁺ [ x ] ord)
inᴿ-joinᴿ⁺ x p lt (0# , rt) bal ord (left ⦃ ord' ⦄ prf) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴿ⁺ x p lt (0# , rt) bal ord (right prf) = prf
inᴿ-joinᴿ⁺ x p lt (1# , rt) ~0 ord (here tt) = ⊥-elim (irrefl⁺ [ x ] ord)
inᴿ-joinᴿ⁺ x p lt (1# , rt) ~0 ord (left ⦃ ord' ⦄ prf) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴿ⁺ x p lt (1# , rt) ~0 ord (right prf) = prf
inᴿ-joinᴿ⁺ x p lt (1# , rt) ~- ord (here tt) = ⊥-elim (irrefl⁺ [ x ] ord)
inᴿ-joinᴿ⁺ x p lt (1# , rt) ~- ord (left ⦃ ord' ⦄ prf) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴿ⁺ x p lt (1# , rt) ~- ord (right prf) = prf
inᴿ-joinᴿ⁺ x p lt (1# , node pᴿ ltᴿ rtᴿ ~+) ~+ ord (here tt) = here ⦃ ord ⦄ tt
inᴿ-joinᴿ⁺ x p lt (1# , node pᴿ ltᴿ rtᴿ ~+) ~+ ord (right prf) = right prf
inᴿ-joinᴿ⁺ x p lt (1# , node pᴿ ltᴿ rtᴿ ~+) ~+ ord (left (here tt)) = ⊥-elim (irrefl⁺ [ x ] ord)
inᴿ-joinᴿ⁺ x p lt (1# , node pᴿ ltᴿ rtᴿ ~+) ~+ ord (left (left ⦃ ord' ⦄ prf)) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴿ⁺ x p lt (1# , node pᴿ ltᴿ rtᴿ ~+) ~+ ord (left (right prf)) = left prf
inᴿ-joinᴿ⁺ x p lt (1# , node pᴿ ltᴿ rtᴿ ~0) ~+ ord (here tt) = here ⦃ ord ⦄ tt
inᴿ-joinᴿ⁺ x p lt (1# , node pᴿ ltᴿ rtᴿ ~0) ~+ ord (right prf) = right prf
inᴿ-joinᴿ⁺ x p lt (1# , node pᴿ ltᴿ rtᴿ ~0) ~+ ord (left (here tt)) = ⊥-elim (irrefl⁺ [ x ] ord)
inᴿ-joinᴿ⁺ x p lt (1# , node pᴿ ltᴿ rtᴿ ~0) ~+ ord (left (left ⦃ ord' ⦄ prf)) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴿ⁺ x p lt (1# , node pᴿ ltᴿ rtᴿ ~0) ~+ ord (left (right prf)) = left prf
inᴿ-joinᴿ⁺ x p lt (1# , node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-) ~+ ord (here tt) =
  left ⦃ mklim rtᴸ ⦄ (here ⦃ ord ⦄  ⦃ mklim rtᴸ ⦄ tt)
inᴿ-joinᴿ⁺ x p lt (1# , node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-) ~+ ord (left (here tt)) = ⊥-elim (irrefl⁺ [ x ] ord)
inᴿ-joinᴿ⁺ x p lt (1# , node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-) ~+ ord (left (left ⦃ ord' ⦄ prf)) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴿ-joinᴿ⁺ x p lt (1# , node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-) ~+ ord (left ⦃ ord' ⦄ (right prf)) =
  left ⦃ trans⁺ [ x ] ord' (mklim rtᴸ) ⦄ (left prf)
inᴿ-joinᴿ⁺ x p lt (1# , node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-) ~+ ord (right (here tt)) = here ⦃ ord ⦄ tt
inᴿ-joinᴿ⁺ x p lt (1# , node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-) ~+ ord (right (left prf)) = left (right prf)
inᴿ-joinᴿ⁺ x p lt (1# , node pᴿ (node pᴸ ltᴸ rtᴸ _) rtᴿ ~-) ~+ ord (right (right prf)) = right prf

inᴸ-joinᴸ⁺ : ∀ {l u : Key⁺} {hl hr h : ℕ}
            (x : Key)
            (p : Key × V)
            ⦃ @erased l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ @erased p<u : [ proj₁ p ] <⁺ u ⦄
            (lt⁺ : ∃ λ i → BOBMap V l [ proj₁ p ] (i ⊕ hl))
            (rt : BOBMap V [ proj₁ p ] u hr)
            (bal : hl ~ hr ⊔ h)
            → [ x ] <⁺ [ proj₁ p ]
            → x ∈ (proj₂ (joinˡ⁺ p lt⁺ rt bal))
            → x ∈ proj₂ lt⁺
inᴸ-joinᴸ⁺ x p (0# , lt) rt bal ord (here tt) = ⊥-elim (irrefl⁺ [ x ] ord)
inᴸ-joinᴸ⁺ x p (0# , lt) rt bal ord (left prf) = prf
inᴸ-joinᴸ⁺ x p (0# , lt) rt bal ord (right ⦃ ord' ⦄ prf) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴸ⁺ x p (1# , lt) rt ~+ ord (here tt) = ⊥-elim (irrefl⁺ [ x ] ord)
inᴸ-joinᴸ⁺ x p (1# , lt) rt ~+ ord (left prf) = prf
inᴸ-joinᴸ⁺ x p (1# , lt) rt ~+ ord (right ⦃ ord' ⦄ prf) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴸ⁺ x p (1# , lt) rt ~0 ord (here tt) = ⊥-elim (irrefl⁺ [ x ] ord)
inᴸ-joinᴸ⁺ x p (1# , lt) rt ~0 ord (left prf) = prf
inᴸ-joinᴸ⁺ x p (1# , lt) rt ~0 ord (right ⦃ ord' ⦄ prf) = ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴸ⁺ x p (1# , node pᴸ ltᴸ rtᴸ ~0) rt ~- ord (here tt) = here ⦃ k≤u = ord ⦄ tt
inᴸ-joinᴸ⁺ x p (1# , node pᴸ ltᴸ rtᴸ ~0) rt ~- ord (left prf) = left prf
inᴸ-joinᴸ⁺ x p (1# , node pᴸ ltᴸ rtᴸ ~0) rt ~- ord (right (here tt)) = ⊥-elim (irrefl⁺ [ x ] ord)
inᴸ-joinᴸ⁺ x p (1# , node pᴸ ltᴸ rtᴸ ~0) rt ~- ord (right (left prf)) = right prf
inᴸ-joinᴸ⁺ x p (1# , node pᴸ ltᴸ rtᴸ ~0) rt ~- ord (right (right ⦃ ord' ⦄ prf)) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴸ⁺ x p (1# , node pᴸ ltᴸ rtᴸ ~-) rt ~- ord (here tt) = here ⦃ k≤u = ord ⦄ tt
inᴸ-joinᴸ⁺ x p (1# , node pᴸ ltᴸ rtᴸ ~-) rt ~- ord (left prf) = left prf
inᴸ-joinᴸ⁺ x p (1# , node pᴸ ltᴸ rtᴸ ~-) rt ~- ord (right (here tt)) = ⊥-elim (irrefl⁺ [ x ] ord)
inᴸ-joinᴸ⁺ x p (1# , node pᴸ ltᴸ rtᴸ ~-) rt ~- ord (right (left prf)) = right prf
inᴸ-joinᴸ⁺ x p (1# , node pᴸ ltᴸ rtᴸ ~-) rt ~- ord (right (right ⦃ ord' ⦄ prf)) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)
inᴸ-joinᴸ⁺ x p (1# , node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ _) ~+) rt ~- ord (here tt) =
  right ⦃ mklim ltᴿ ⦄ (here ⦃ mklim ltᴿ ⦄ ⦃ ord ⦄ tt)
inᴸ-joinᴸ⁺ x p (1# , node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ _) ~+) rt ~- ord (left (here tt)) = here ⦃ k≤u = ord ⦄ tt
inᴸ-joinᴸ⁺ x p (1# , node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ _) ~+) rt ~- ord (left (left prf)) = left prf
inᴸ-joinᴸ⁺ x p (1# , node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ _) ~+) rt ~- ord (left (right prf)) = right (left prf)
inᴸ-joinᴸ⁺ x p (1# , node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ _) ~+) rt ~- ord (right (here tt)) = ⊥-elim (irrefl⁺ [ x ] ord)
inᴸ-joinᴸ⁺ x p (1# , node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ _) ~+) rt ~- ord (right ⦃ ord' ⦄ (left prf)) =
  right ⦃ trans⁺ [ proj₁ pᴸ ] (mklim ltᴿ) ord' ⦄ (right prf)
inᴸ-joinᴸ⁺ x p (1# , node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ _) ~+) rt ~- ord (right (right ⦃ ord' ⦄ prf)) =
  ⊥-elim (asym [ ord ]-lower [ ord' ]-lower)

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
