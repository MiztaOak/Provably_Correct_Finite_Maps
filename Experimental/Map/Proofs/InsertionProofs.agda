{-# OPTIONS --erasure #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet using (OrdSet; toStrictTotalOrder)

module Map.Proofs.InsertionProofs {k ℓ₁ v} (order : OrdSet k ℓ₁) (V : Set v) where
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
open import Map.Proofs.Proofs order V renaming (⊥-elimErased to ⊥-elim)


---------------------------------------------------------------------------------
-- lookup∈ : Lookup function that uses a proof of membership to gurantee a value
---------------------------------------------------------------------------------
lookup∈ : ∀ {l u : Key⁺} {h : ℕ} {k : Key} {m : BOBMap V l u h}
          → k ∈ m → V
lookup∈ {k = k} {node .(k , _) lm rm bal} (here {v = v} x) = v
lookup∈ {k = k} {node p lm rm bal} (left prf) = lookup∈ prf
lookup∈ {k = k} {node p lm rm bal} (right prf) = lookup∈ prf

---------------------------------------------------------------------------------
-- ∈⇒lookup
---------------------------------------------------------------------------------
∈⇒lookup : ∀ {l u : Key⁺} {h : ℕ} (m : BOBMap V l u h) (k : Key) {v : V}
                   → lookup m k ≡ just v
                   → k ↦ v ∈ m
∈⇒lookup (node p lm rm bal) k prf with compare k (proj₁ p)
... | tri< a _ _    = left ⦃ [ a ]ᴿ ⦄ (∈⇒lookup lm k prf)
... | tri≈ _ refl _ = here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ (sym $ eqFromJust prf)
... | tri> _ _ c    = right ⦃ [ c ]ᴿ ⦄ (∈⇒lookup rm k prf)

---------------------------------------------------------------------------------
-- lookup⇒∈
---------------------------------------------------------------------------------
lookup⇒∈ : ∀ {l u : Key⁺} {h : ℕ} (k : Key) {v : V} (m : BOBMap V l u h)
            → k ↦ v ∈ m
            → lookup m k ≡ just v
lookup⇒∈ k (node .(k , _) lm rm bal) (here refl) with compare k k
... | tri< _ ¬b _   = ⊥-elim (¬b refl)
... | tri≈ _ refl _ = refl
... | tri> _ ¬b _   = ⊥-elim (¬b refl)
lookup⇒∈ k (node p lm rm bal) (left {{ord}} prf) with compare k (proj₁ p)
... | tri< _ _ _    = lookup⇒∈ k lm prf
... | tri≈ _ refl _ = ⊥-elim (irrefl⁺ [ proj₁ p ] ord)
... | tri> ¬a _ _   = ⊥-elim (¬a [ ord ]-lower)
lookup⇒∈ k (node p lm rm bal) (right {{ord}} prf) with compare k (proj₁ p)
... | tri< _ _ ¬c   = ⊥-elim (¬c [ ord ]-lower)
... | tri≈ _ refl _ = ⊥-elim (irrefl⁺ [ proj₁ p ] ord)
... | tri> _ _ _    = lookup⇒∈ k rm prf

---------------------------------------------------------------------------------
-- lookup-insert
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

lookup-insert : ∀ {l u : Key⁺} {h : ℕ} (k : Key)
                {{l≤k : l <⁺ [ k ]}} {{k≤u : [ k ] <⁺ u}}
                → (m : BOBMap V l u h)
                → (f : Maybe V → V)
                → lookup (proj₂ (insertWith k f m)) k ≡ just (f (lookup m k))
lookup-insert k leaf f with compare k k
... | tri< _ ¬b _   = ⊥-elim (¬b refl)
... | tri≈ _ refl _ = refl
... | tri> _ ¬b _   = ⊥-elim (¬b refl)
lookup-insert k ⦃ l<k ⦄ ⦃ k<u ⦄ (node p lm rm b) f with compare k (proj₁ p) in cmp
... | tri< a _ _ rewrite joinˡ⁺-lookup k p (insertWith k f ⦃ l<k ⦄ ⦃ [ a ]ᴿ ⦄ lm) rm b a =
  lookup-insert k ⦃ k≤u = [ a ]ᴿ ⦄ lm f
... | tri≈ _ refl _ rewrite cmp = refl
... | tri> _ _ c rewrite joinʳ⁺-lookup k p lm (insertWith k f ⦃ [ c ]ᴿ ⦄ ⦃ k<u ⦄ rm) b c =
  lookup-insert k ⦃ [ c ]ᴿ ⦄ rm f

---------------------------------------------------------------------------------
-- Prove that Insert results in ∈
---------------------------------------------------------------------------------
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

insert∈ : ∀ {l u : Key⁺} {h : ℕ} (k : Key) (v : V)
          {{l<k : l <⁺ [ k ]}} {{ k<u : [ k ] <⁺ u}}
          → (m : BOBMap V l u h)
          → k ↦ v ∈ (proj₂ $ insertWith k (λ _ → v) m)
insert∈ k v leaf = here refl
insert∈ k v ⦃ l<k ⦄ ⦃ k<u ⦄ (node p lm rm bal) with compare k (proj₁ p) in cmp
... | tri< a _ _ =
   anyᴸjoinᴸ⁺ (insertWith k (λ _ → v) ⦃ l<k ⦄ ⦃ [ a ]ᴿ ⦄ lm) rm bal [ a ]ᴿ (insert∈ k v ⦃ l<k ⦄ ⦃ [ a ]ᴿ ⦄ lm)
... | tri≈ _ refl _ rewrite cmp = here refl
... | tri> _ _ c =
  anyᴿjoinᴿ⁺ lm (insertWith k (λ _ → v) ⦃ [ c ]ᴿ ⦄ ⦃ k<u ⦄ rm) bal [ c ]ᴿ (insert∈ k v ⦃ [ c ]ᴿ ⦄ ⦃ k<u ⦄ rm)

---------------------------------------------------------------------------------
-- Insert-Safe
---------------------------------------------------------------------------------
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

insert-safe : ∀ {k k' : Key} {v v' : V} {l u : Key⁺} {h : ℕ}
              {{@erased l<k' : l <⁺ [ k' ]}} {{@erased k'<u : [ k' ] <⁺ u}}
              {m : BOBMap V l u h}
              → k ↦ v ∈ m
              → k ≢ k'
              → k ↦ v ∈ proj₂ (insert (k' , v') m)
insert-safe {k} {k'} {v} {v'} ⦃ l<k' = l<k' ⦄ {m = node .(k , _) lm rm bal} (here refl) nEq with
  compare k' k
... | tri< a _ _    = herejoinᴸ⁺ (insertWith k' (λ _ → v') ⦃ l<k' ⦄ ⦃ [ a ]ᴿ ⦄ lm) rm bal
... | tri≈ _ refl _ = ⊥-elim (nEq refl)
... | tri> _ _ c    = herejoinᴿ⁺ lm (insertWith k' (λ _ → v') ⦃ [ c ]ᴿ ⦄ rm) bal
insert-safe {k} {k'} {v} {v'} ⦃ l<k' ⦄ {m = node p lm rm bal} (left ⦃ o ⦄ prf) nEq with compare k' (proj₁ p)
... | tri< a _ _ = anyᴸjoinᴸ⁺ (insertWith k' (λ _ → v') ⦃ p≤u = [ a ]ᴿ ⦄ lm) rm bal o
                             (insert-safe ⦃ k'<u =  [ a ]ᴿ ⦄ prf nEq)
... | tri≈ _ refl _ = left prf
... | tri> _ _ c = anyᴸjoinᴿ⁺ lm (insertWith k' (λ _ → v') ⦃ [ c ]ᴿ ⦄ rm) bal o prf
insert-safe {k} {k'} {v} {v'} {m = node p lm rm bal} (right ⦃ ord ⦄ prf) nEq with compare k' (proj₁ p)
... | tri< a _ _ = anyᴿjoinᴸ⁺ (insertWith k' (λ _ → v') ⦃ p≤u = [ a ]ᴿ ⦄ lm) rm bal ord prf
... | tri≈ _ refl _ = right prf
... | tri> _ _ c =
  anyᴿjoinᴿ⁺ lm (insertWith k' (λ _ → v') ⦃ [ c ]ᴿ ⦄ rm) bal ord (insert-safe ⦃ [ c ]ᴿ ⦄ prf nEq)

---------------------------------------------------------------------------------
-- ∈-ins
---------------------------------------------------------------------------------
postulate
  in-joinᴸ⁺ : ∀ {l u : Key⁺} {hl hr h : ℕ}
              (x : Key)
              (p : Key × V)
              ⦃ @erased l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ @erased p<u : [ proj₁ p ] <⁺ u ⦄
              (lt⁺ : ∃ λ i → BOBMap V l [ proj₁ p ] (i ⊕ hl))
              (rt : BOBMap V [ proj₁ p ] u hr)
              (bal : hl ~ hr ⊔ h)
              → x ∈ (proj₂ (joinˡ⁺ p lt⁺ rt bal))
              → x ∈ proj₂ lt⁺
  in-joinᴿ⁺ : ∀ {l u : Key⁺} {hl hr h : ℕ}
              (x : Key)
              (p : Key × V)
              ⦃ @erased l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ @erased p<u : [ proj₁ p ] <⁺ u ⦄
              (lt : BOBMap V l [ proj₁ p ] hl)
              (rt⁺ : ∃ λ i → BOBMap V [ proj₁ p ] u (i ⊕ hr))
              (bal : hl ~ hr ⊔ h)
              → x ∈ (proj₂ (joinʳ⁺ p lt rt⁺ bal))
              → x ∈ proj₂ rt⁺

∈-ins : ∀ {l u : Key⁺} {h : ℕ}
        (k x : Key)
        (f : Maybe V → V)
        {{@erased l<k : l <⁺ [ k ]}} {{@erased k<u : [ k ] <⁺ u}}
        (m : BOBMap V l u h)
        → x ∈ proj₂ (insertWith k f m)
        → (x ≡ k) ⊎ x ∈ m
∈-ins k .k f leaf (here x) = inj₁ refl
∈-ins k x f ⦃ l<k ⦄ (node p lm rm bal) prf with compare k (proj₁ p)
... | tri< a _ _ with in-joinᴸ⁺ x p ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ (insertWith k f ⦃ p≤u = [ a ]ᴿ ⦄ lm) rm bal prf
... | prfᴸ with ∈-ins k x f ⦃ l<k ⦄ ⦃ [ a ]ᴿ ⦄ lm prfᴸ
... | inj₁ prf = inj₁ prf
... | inj₂ prf = inj₂ (left ⦃ {!!} ⦄ prf)
∈-ins k x f ⦃ k<u = k<u ⦄ (node p lm rm bal) prf
  | tri> _ _ c with in-joinᴿ⁺ x p ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lm (insertWith k f ⦃ [ c ]ᴿ ⦄ rm) bal prf
... | prfᴿ with ∈-ins k x f ⦃ [ c ]ᴿ ⦄ ⦃ k<u ⦄ rm prfᴿ
... | inj₁ prf = inj₁ prf
... | inj₂ prf = inj₂ (right ⦃ {!!} ⦄ prf)
∈-ins k x f ⦃ l<k ⦄ (node p lm rm bal) prf
  | tri≈ _ refl _ with prf
... | left pf = inj₂ (left pf)
... | here tt = inj₁ refl
... | right pf = inj₂ (right pf)

---------------------------------------------------------------------------------
-- ins-comm
---------------------------------------------------------------------------------
{-
ins-comm : ∀ {l u : Key⁺} {h : ℕ}
           (x y : Key)
           {{l<x : l <⁺ [ x ]}} {{x<u : [ x ] <⁺ u}}
           {{l<y : l <⁺ [ y ]}} {{y<u : [ y ] <⁺ u}}
           (fˣ fʸ : Maybe V → V)
           (m : BOBMap V l u h)
           → x ≢ y
           → (∀ z v → z ↦ v ∈ proj₂ (insertWith x fˣ (proj₂ (insertWith y fʸ m)))
             → z ↦ v ∈ proj₂ (insertWith y fʸ (proj₂ (insertWith x fˣ m))))
ins-comm x y fˣ fʸ m nEq z v prf = {!!}
-- -}
-- -}
-- -}
-- -}

---------------------------------------------------------------------------------
-- Convert _↦_∈_ to _∈_
---------------------------------------------------------------------------------
↦∈To∈ : ∀ {l u : Key⁺} {h : ℕ} {k : Key} {v : V} {m : BOBMap V l u h}
          → k ↦ v ∈ m → k ∈ m
↦∈To∈ (here x) = here tt
↦∈To∈ (left prf) = left (↦∈To∈ prf)
↦∈To∈ (right prf) = right (↦∈To∈ prf)
