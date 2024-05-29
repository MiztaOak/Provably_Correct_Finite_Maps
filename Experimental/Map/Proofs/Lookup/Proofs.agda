{-# OPTIONS --erasure #-}
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet using (OrdSet; toStrictTotalOrder)

module Map.Proofs.Lookup.Proofs {k ℓ₁ v} (order : OrdSet k ℓ₁) (V : Set v) where
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; ∃; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality hiding (trans; [_])
open import Data.Maybe.Base hiding (map)
open import Relation.Binary.Definitions
open import Function.Base

open import Prelude
open import Map.BOBMap order as BOB
open import Map.Proofs.Proofs order V
open StrictTotalOrder (toStrictTotalOrder order) renaming (Carrier to Key)
open import Map.Proofs.Lookup.Helpers order V

---------------------------------------------------------------------------------
-- lookup∈ : Lookup function that uses a proof of membership to gurantee a value
---------------------------------------------------------------------------------
lookup∈ : ∀ {l u : Key⁺} {h : ℕ} {k : Key} {m : BOBMap V l u h}
          → k ∈ m → V
lookup∈ {k = k} {node .(k , _) lm rm bal} (here {v = v} x) = v
lookup∈ {k = k} {node p lm rm bal} (left prf) = lookup∈ prf
lookup∈ {k = k} {node p lm rm bal} (right prf) = lookup∈ prf

---------------------------------------------------------------------------------
-- mapsTo
---------------------------------------------------------------------------------
mapsTo : ∀ {l u : Key⁺} {h : ℕ} {m : BOBMap V l u h} {k : Key}
  → (k∈m : k ∈ m) → k ↦ (lookup∈ k∈m) ∈ m
mapsTo (here x)    = here refl
mapsTo (left prf)  = left (mapsTo prf)
mapsTo (right prf) = right (mapsTo prf)

---------------------------------------------------------------------------------
-- ∉⇒nothing
---------------------------------------------------------------------------------
∉⇒nothing : ∀ {l u : Key⁺} {h : ℕ} {m : BOBMap V l u h} {k : Key}
  → k ∉ m → lookup m k ≡ nothing
∉⇒nothing {m = leaf} {k} prf = refl
∉⇒nothing {m = node p lm rm bal} {k} k∉m with compare k (proj₁ p)
... | tri< k<p _ _ = ∉⇒nothing (∉Left k<p k∉m)
... | tri≈ _ refl _ = ⊥-elim (k∉m (here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ tt))
... | tri> _ _ p<k = ∉⇒nothing (∉Right p<k k∉m)

---------------------------------------------------------------------------------
-- ∉⇒nothing
---------------------------------------------------------------------------------
nothing⇒∉ : ∀ {l u : Key⁺} {h : ℕ} {m : BOBMap V l u h} {k : Key}
  → (lookup m k ≡ nothing) → k ∉ m
nothing⇒∉ {m = leaf} {k} eq ()
nothing⇒∉ {m = node p lm rm bal} {k} eq (left ⦃ k<p ⦄ prf ) with compare k (proj₁ p)
... | tri< k<p _ _ = nothing⇒∉ eq prf
nothing⇒∉ {m = node p _ _ _} {.(proj₁ p)} () (left prf) | tri≈ _ refl _
... | tri> ¬k<p _ _ = ⊥-elim (¬k<p [ k<p ]-lower)
nothing⇒∉ {m = node p lm rm bal} {k} eq (here tt) with compare k (proj₁ p)
... | tri< _ k≢p _ = ⊥-elim (k≢p refl)
nothing⇒∉ {m = node .(k , _) _ _ _} {k} () (here tt) | tri≈ _ refl _
... | tri> _ k≢p _ = ⊥-elim (k≢p refl)
nothing⇒∉ {m = node p lm rm bal} {k} eq (right ⦃ p<k ⦄ prf) with compare k (proj₁ p)
... | tri< _ _ ¬p<k = ⊥-elim (¬p<k [ p<k ]-lower)
nothing⇒∉ {m = node p _ _ _} {.(proj₁ p)} () (right prf) | tri≈ _ refl _
... | tri> _ _ p<k = nothing⇒∉ eq prf

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
lookup-insert : ∀ {l u : Key⁺} {h : ℕ} (k : Key)
                {{@erased l≤k : l <⁺ [ k ]}} {{@erased k≤u : [ k ] <⁺ u}}
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
-- lookup≡lookup∈ proof that lookup and lookup∈ are equivivalent
---------------------------------------------------------------------------------
lookup≡lookup∈ : ∀ {l u : Key⁺} {h : ℕ} (k : Key)
  ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
  → (m : BOBMap V l u h)
  → (k∈m : k ∈ m)
  → just (lookup∈ k∈m) ≡ lookup m k
lookup≡lookup∈ k (node (.k , v) _ _ _) (here x) with compare k k
... | tri< _ ¬b _ = ⊥-elim (¬b refl)
... | tri≈ _ refl _ = refl
... | tri> _ ¬b _ = ⊥-elim (¬b refl)
lookup≡lookup∈ k (node (k' , v) lm _ _) (left ⦃ k<k' ⦄ prf) with compare k k'
... | tri< _ _ _ = lookup≡lookup∈ k lm prf
... | tri≈ ¬k<k' _ _ = ⊥-elim (¬k<k' [ k<k' ]-lower)
... | tri> ¬k<k' _ _ = ⊥-elim (¬k<k' [ k<k' ]-lower)
lookup≡lookup∈ k (node (k' , v) _ rm _) (right ⦃ k>k' ⦄ prf) with compare k k'
... | tri< _ _ ¬k>k' = ⊥-elim (¬k>k' [ k>k' ]-lower)
... | tri≈ _ _ ¬k>k' = ⊥-elim (¬k>k' [ k>k' ]-lower)
... | tri> _ _ _ = lookup≡lookup∈ k rm prf
