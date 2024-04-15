{-# OPTIONS --erasure #-}
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet

module Map.Proofs.Lookup.Helpers {k ℓ₁ ℓ} (order : OrdSet k ℓ₁) (V : Set ℓ) where
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; ∃; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality hiding (trans; [_])
open import Relation.Binary.Definitions

open import Map.BOBMap order as BOB
open import Map.Proofs.Proofs order V
open StrictTotalOrder (toStrictTotalOrder order) renaming (Carrier to Key)
---------------------------------------------------------------------------------
-- join left and right lemmas for insertion
---------------------------------------------------------------------------------
joinˡ⁺-lookup : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (k : Key)
    (p : Key × V)
    (lt⁺ : ∃ (λ i → BOBMap V l [ proj₁ p ] (i ⊕ hl)))
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → @erased k < proj₁ p
    → lookup (proj₂ (joinˡ⁺ p lt⁺ rt bal)) k ≡ lookup (proj₂ lt⁺) k
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
  → @erased proj₁ p < k
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
