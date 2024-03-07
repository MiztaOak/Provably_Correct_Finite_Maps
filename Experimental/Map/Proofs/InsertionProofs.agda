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
... | tri≈ _ refl _ = ⊥-elim (asym k>R {!mapOrd ltᴿ!})
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
{-
variable
  p : K × V
  l r : Ext K
  h hl hr : ℕ
  bal : hl ~ hr ⊔ h
  lt rt : BOBMap (l , r) h
  lt⁺ :  ∃ (λ i → BOBMap (l , r) (i ⊕ hl))
lookup-insert∈ : ∀ {l u : Ext K} {h : ℕ} (k : K)
                 {{l≤k : l ≺Ex # k}} {{k≤u : # k ≺Ex u}}
                 (m : BOBMap (l , u) h)
                 → (f : Maybe V → V)
                 → lookup (proj₂ (insertWith k f m)) k ≡ just (f (lookup m k))
lookup-insert∈ k Map.BOBMap.Map.leaf f rewrite compareSelf k = refl
-- lookup-insert∈ k Map.BOBMap.Map.leaf f with compare k k | compareSelf k
-- ... | .eq | refl = refl
lookup-insert∈ k (Map.BOBMap.Map.node p m m₁ bal) f with compare k (proj₁ p)
... | eq rewrite compareSelf (proj₁ p) = refl
... | inj₁ (! {{prf}}) rewrite lem {p = p} {lt⁺ = insertWith k f m} {rt = m₁} {bal = bal}  prf = lookup-insert∈ k m f
... | ge = {!!}

lookup-insert∉ : ∀ {l u : Ext K} {h : ℕ} → (k : K)
                 → {{l≤k : l ≺Ex # k}} {{k≤u : # k ≺Ex u}}
                 → (m : BOBMap (l , u) h)
                 → (f : Maybe V → V)
                 → k ∉ m
                 → lookup (proj₂ (insertWith k f m)) k ≡ just (f nothing)
lookup-insert∉ {l} {u} k {{l≤k}} {{k≤u}} leaf f prf
  with insertWith {l} {u} k f {{l≤k}} {{k≤u}} leaf
... | _ , res with compare k k | compareSelf k
... | .eq | refl = refl
lookup-insert∉ k (node p lm rm bal) f prf with compare k (proj₁ p) in comp
lookup-insert∉ k (node p lm rm bal) f prf
  | le with lookup-insert∉ k lm f (¬Left prf)
... | x with insertWith k f lm
... | 1# , lm' with bal
lookup-insert∉ k (node p lm rm bal) f prf
  | le | x | 1# , lm' | ~+ with compare k (proj₁ p)
... | le = x
lookup-insert∉ k (node p lm rm bal) f prf
  | le | x | 1# , lm' | ~0 with compare k (proj₁ p)
... | le = x
lookup-insert∉ k (node p lm rm bal) f prf
  | le | x | 1# , lm' | ~- = {!!}
lookup-insert∉ k (node p lm rm bal) f prf
  | le | x | 0# , lm' with compare k (proj₁ p)
... | le = x
lookup-insert∉ k (node p lm rm bal) f prf
  | eq with prf (here tt)
... | ()
lookup-insert∉ k (node p lm rm bal) f prf
  | ge with lookup-insert∉ k rm f (¬Right prf)
... | x with insertWith k f rm
... | 1# , rm' with bal
lookup-insert∉ k (node p lm rm bal) f prf
  | ge | x | 1# , rm' | ~+ = {!!}
lookup-insert∉ k (node p lm rm bal) f prf
  | ge | x | 1# , rm' | ~0 with compare k (proj₁ p)
... | ge = x
lookup-insert∉ k (node p lm rm bal) f prf
  | ge | x | 1# , rm' | ~- with compare k (proj₁ p)
... | ge = x
lookup-insert∉ k (node p lm rm bal) f prf
  | ge | x | 0# , rm' with compare k (proj₁ p)
... | ge = x
-}

---------------------------------------------------------------------------------
-- Prove that Insert results in ∈
---------------------------------------------------------------------------------
insert∈ : ∀ {l u : Key⁺} {h : ℕ} (k : Key) (v : V)
          {{l<k : l <⁺ [ k ]}} {{ k<u : [ k ] <⁺ u}}
          → (m : BOBMap V l u h)
          → k ↦ v ∈ (proj₂ $ insertWith k (λ _ → v) m)
insert∈ k v leaf = here refl
insert∈ k v (node p lm rm bal) with compare k (proj₁ p) in cmp
... | tri< a ¬b ¬c = {!insert∈ k v ⦃ ? ⦄ ⦃ ? ⦄ lm!}
... | tri≈ ¬a refl ¬c rewrite cmp = here refl
... | tri> ¬a ¬b c = {!!}

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
