{-# OPTIONS --erasure #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet using (OrdSet; toStrictTotalOrder)

module Map.Proofs.InsertionProofs {k ℓ₁ v} (order : OrdSet k ℓ₁) (V : Set v) where
open import Data.Nat.Base using (ℕ; _*_; suc; zero)
open import Data.Empty
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
... | tri≈ _ refl _ = here ⦃ mapOrd lm ⦄ ⦃ mapOrd rm ⦄ (sym $ eqFromJust prf)
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
... | tri< a ¬b ¬c = ⊥-elim (asym a {!mapOrd ltᴿ!}) -- proof erasure causes problem here
... | tri≈ ¬a refl _ = ⊥-elim (¬a {!mapOrd ltᴿ!}) -- could maybe try proving that BOBMap V l l h is absurd?
... | tri> _ _ _ rewrite cmpᴿ = refl
joinˡ⁺-lookup k p (1# , (node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ b) ~+)) rt ~- ord
  | tri> _ _ k>R with compare k (proj₁ p)
... | tri≈ ¬a refl ¬c = ⊥-elim (irrefl refl ord)
... | tri> ¬a _ _ = ⊥-elim (¬a ord)
... | tri< k<p _ _ with compare k (proj₁ pᴸ)
... | tri< k<L ¬b ¬c = {!!} -- yea no clue how to solve this hole right now
... | tri≈ _ refl _ = ⊥-elim (asym k>R {!!})
... | tri> _ _ _ rewrite cmpᴿ = refl

postulate
  lemL : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (k : Key)
    (p : Key × V)
    (lt⁺ : ∃ (λ i → BOBMap V l [ proj₁ p ] (i ⊕ hl)))
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → k < proj₁ p → lookup (proj₂ (joinˡ⁺ p lt⁺ rt bal)) k ≡ lookup (proj₂ lt⁺) k
  lemR : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (k : Key)
    (p : Key × V)
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt⁺ : ∃ (λ i → BOBMap V [ proj₁ p ] u (i ⊕ hr)))
    (bal : hl ~ hr ⊔ h)
    → proj₁ p < k → lookup (proj₂ (joinʳ⁺ p lt rt⁺ bal)) k ≡ lookup (proj₂ rt⁺) k

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
... | tri< a _ _ rewrite lemL k p (insertWith k f ⦃ l<k ⦄ ⦃ [ a ]ᴿ ⦄ lm) rm b a =
  lookup-insert k ⦃ k≤u = [ a ]ᴿ ⦄ lm f
... | tri≈ _ refl _ rewrite cmp = refl
... | tri> _ _ c rewrite lemR k p lm (insertWith k f ⦃ [ c ]ᴿ ⦄ ⦃ k<u ⦄ rm) b c =
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
    → [ k ] <⁺ [ proj₁ p ]
    → Any (_≡_ v) k (proj₂ lt⁺)
    → Any (_≡_ v) k (proj₂ (joinˡ⁺ p lt⁺ rt bal))
anyᴸjoinᴸ⁺ (0# , lt) rt bal ord prf = left ⦃ ord ⦄ prf
anyᴸjoinᴸ⁺ (1# , lt) rt ~+ ord prf = left ⦃ ord ⦄ prf
anyᴸjoinᴸ⁺ (1# , lt) rt ~0 ord prf = left ⦃ ord ⦄ prf
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ rtᴸ ~-)) rt ~- ord (here ⦃ o₁ ⦄ refl) = here ⦃ o₁ ⦄ ⦃ {!!} ⦄ refl
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ rtᴸ ~-)) rt ~- ord (left prf) = left prf
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ rtᴸ ~-)) rt ~- ord (right prf) = right (left ⦃ ord ⦄ prf)
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ rtᴸ ~0)) rt ~- ord (here ⦃ o₁ ⦄ refl) = here ⦃ o₁ ⦄ ⦃ {!!} ⦄ refl
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ rtᴸ ~0)) rt ~- ord (left prf) = left prf
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ rtᴸ ~0)) rt ~- ord (right prf) = right (left ⦃ ord ⦄ prf)
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ b) ~+)) rt ~- ord (here ⦃ o₁ ⦄ refl) =
  left ⦃ {!!} ⦄ (here ⦃ o₁ ⦄ ⦃ {!!} ⦄ refl)
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ b) ~+)) rt ~- ord (left prf) = left ⦃ {!!} ⦄ (left prf)
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ b) ~+)) rt ~- ord (right (here refl)) =
  here ⦃ {!!} ⦄ ⦃ {!!} ⦄ refl
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ b) ~+)) rt ~- ord (right (left prf)) = left (right prf)
anyᴸjoinᴸ⁺ (1# , (node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ b) ~+)) rt ~- ord (right (right prf)) = right (left ⦃ ord ⦄ prf)

anyᴿjoinᴸ⁺ : ∀ {l u : Key⁺} {hl hr h : ℕ}
    {k : Key}
    {v : V}
    {p : Key × V}
    (lt⁺ : ∃ (λ i → BOBMap V l [ proj₁ p ] (i ⊕ hl)))
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → [ proj₁ p ] <⁺ [ k ]
    → Any (_≡_ v) k rt
    → Any (_≡_ v) k (proj₂ (joinˡ⁺ p lt⁺ rt bal))
anyᴿjoinᴸ⁺ (0# , lt) rt b ord prf = right ⦃ ord ⦄ prf
anyᴿjoinᴸ⁺ (1# , lt) rt ~+ ord prf = right ⦃ ord ⦄ prf
anyᴿjoinᴸ⁺ (1# , lt) rt ~0 ord prf = right ⦃ ord ⦄ prf
anyᴿjoinᴸ⁺ (1# , (node pᴸ ltᴸ rtᴸ ~-)) rt ~- ord prf = right ⦃ {!!} ⦄ (right ⦃ ord ⦄ prf)
anyᴿjoinᴸ⁺ (1# , (node pᴸ ltᴸ rtᴸ ~0)) rt ~- ord prf = right ⦃ {!!} ⦄ (right ⦃ ord ⦄ prf)
anyᴿjoinᴸ⁺ (1# , (node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ _) ~+)) rt ~- ord prf = right ⦃ {!!} ⦄ (right ⦃ ord ⦄ prf)

postulate
  anyJoinL : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (k : Key)
    (v : V)
    (p : Key × V)
    (lt⁺ : ∃ (λ i → BOBMap V l [ proj₁ p ] (i ⊕ hl)))
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → Any (_≡_ v) k (proj₂ lt⁺)
    → Any (_≡_ v) k (proj₂ (joinˡ⁺ p lt⁺ rt bal))
  anyJoinR : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (k : Key)
    (v : V)
    (p : Key × V)
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt⁺ : ∃ (λ i → BOBMap V [ proj₁ p ] u (i ⊕ hr)))
    (bal : hl ~ hr ⊔ h)
    → Any (_≡_ v) k (proj₂ rt⁺)
    → Any (_≡_ v) k (proj₂ (joinʳ⁺ p lt rt⁺ bal))

insert∈ : ∀ {l u : Key⁺} {h : ℕ} (k : Key) (v : V)
          {{l<k : l <⁺ [ k ]}} {{ k<u : [ k ] <⁺ u}}
          → (m : BOBMap V l u h)
          → k ↦ v ∈ (proj₂ $ insertWith k (λ _ → v) m)
insert∈ k v leaf = here refl
insert∈ k v ⦃ l<k ⦄ ⦃ k<u ⦄ (node p lm rm bal) with compare k (proj₁ p) in cmp
... | tri< a ¬b ¬c =
   anyᴸjoinᴸ⁺ (insertWith k (λ _ → v) ⦃ l<k ⦄ ⦃ [ a ]ᴿ ⦄ lm) rm bal [ a ]ᴿ (insert∈ k v ⦃ l<k ⦄ ⦃ [ a ]ᴿ ⦄ lm)
... | tri≈ ¬a refl ¬c rewrite cmp = here refl
... | tri> ¬a ¬b c =
  anyJoinR k v p lm (insertWith k (λ _ → v) ⦃ [ c ]ᴿ ⦄ ⦃ k<u ⦄ rm) bal (insert∈ k v ⦃ [ c ]ᴿ ⦄ ⦃ k<u ⦄ rm)

---------------------------------------------------------------------------------
-- Insert-Safe
---------------------------------------------------------------------------------
insert-safe : ∀ {k k' : Key} {v v' : V} {l u : Key⁺} {h : ℕ}
              {{l<k' : l <⁺ [ k' ]}} {{k'<u : [ k' ] <⁺ u}}
              {m : BOBMap V l u h}
              → k ↦ v ∈ m
              → k ≢ k'
              → k ↦ v ∈ proj₂ (insert (k' , v') m)
insert-safe {k} {k'} {v} {v'} {m = node .(k , _) lm rm bal} (here ⦃ l<k ⦄ ⦃ k<u ⦄ refl) nEq with
  compare k' k
... | tri< a _ _    = {!!}
... | tri≈ _ refl _ = ⊥-elim (nEq refl)
... | tri> _ _ c    = {!!}
insert-safe {k} {k'} {v} {v'} ⦃ l<k' ⦄ {m = node p lm rm bal} (left prf) nEq with compare k' (proj₁ p)
... | tri< a ¬b ¬c =
  anyJoinL k v p (insertWith k' (λ _ → v') ⦃ p≤u = [ a ]ᴿ ⦄ lm) rm bal
    (insert-safe ⦃ k'<u =  [ a ]ᴿ ⦄ prf nEq)
... | tri≈ ¬a refl ¬c = left prf
... | tri> ¬a ¬b c = {! !}
insert-safe {k} {k'} {v} {v'} {m = node p lm rm bal} (right ⦃ ord ⦄ prf) nEq with compare k' (proj₁ p)
... | tri< a ¬b ¬c = anyᴿjoinᴸ⁺ (insertWith k' (λ _ → v') ⦃ p≤u = {!!} ⦄ lm) rm bal [ [ ord ]-lower ]ᴿ prf
... | tri≈ ¬a refl ¬c = right prf
... | tri> ¬a ¬b c =
  anyJoinR k v p lm (insertWith k' (λ _ → v') ⦃ [ c ]ᴿ ⦄ rm) bal (insert-safe ⦃ [ c ]ᴿ ⦄ prf nEq)

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
