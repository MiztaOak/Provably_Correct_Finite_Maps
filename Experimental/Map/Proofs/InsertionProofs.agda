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
open import Map.Proofs.Proofs order V

---------------------------------------------------------------------------------
-- Induction Principle using insert
---------------------------------------------------------------------------------
ip-insert : ∀ {l u : Key⁺} --⦃ @erased l<u : l <⁺ u ⦄
            (P : {h : ℕ} → BOBMap V l u h → Set (k ⊔ v))
            → (∀ (m : BOBMap V l u 0) → P m )
            × (∀ {h} → (m : BOBMap V l u h)
                 → P m
                 → ∀ k v
                 → ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
                 → k ∉ m
                 → P (proj₂ (insertWith k (λ _ → v) ⦃ l<k ⦄ ⦃ k<u ⦄ m)))
            → (∀ {h} → (m : BOBMap V l u h) → P m)
ip-insert P (base , step) leaf = base leaf
ip-insert P (base , step) (node p lm rm bal) = {!!}


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
∈-ins : ∀ {l u : Key⁺} {h : ℕ}
        (k x : Key)
        (f : Maybe V → V)
        {{@erased l<k : l <⁺ [ k ]}} {{@erased k<u : [ k ] <⁺ u}}
        (m : BOBMap V l u h)
        → x ∈ proj₂ (insertWith k f m)
        → (x ≡ k) ⊎ x ∈ m
∈-ins k .k f leaf (here x) = inj₁ refl
∈-ins k x f ⦃ l<k ⦄ (node p lm rm bal) prf with compare k x
... | tri≈ _ refl _ = inj₁ refl
∈-ins k x f ⦃ l<k ⦄ (node p lm rm bal) prf | tri< k<x _ _ with compare k (proj₁ p)
∈-ins k x f ⦃ l<k ⦄ (node p lm rm bal) prf | tri< k<x _ _ | tri< k<p _ _ with compare x (proj₁ p)
... | tri≈ _ refl _ = inj₂ (here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ tt)
... | tri> _ _ c = inj₂ (right ⦃ [ c ]ᴿ ⦄ (inᴿ-joinᴸ⁺ x p ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lt⁺ rm bal [ c ]ᴿ prf))
  where
    lt⁺ = insertWith k f ⦃ p≤u = [ k<p ]ᴿ ⦄ lm
... | tri< x<p _ _ with ∈-ins k x f ⦃ k<u = [ k<p ]ᴿ ⦄ lm prf'
  where
    lt⁺ = insertWith k f ⦃ p≤u = [ k<p ]ᴿ ⦄ lm
    prf' = inᴸ-joinᴸ⁺ x p ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lt⁺ rm bal [ x<p ]ᴿ prf
... | inj₁ prf = inj₁ prf
... | inj₂ prf = inj₂ (left ⦃ [ x<p ]ᴿ ⦄ prf)
∈-ins k x f ⦃ l<k ⦄ ⦃ k<u ⦄ (node p lm rm bal) prf | tri< k<x _ _ | tri> _ _ p<k with compare x (proj₁ p)
... | tri< a _ _ = inj₂ (left ⦃ [ a ]ᴿ ⦄ (inᴸ-joinᴿ⁺ x p ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lm rt⁺ bal [ a ]ᴿ prf))
  where
    rt⁺ = insertWith k f ⦃ [ p<k ]ᴿ ⦄ rm
... | tri≈ _ refl _ = inj₂ (here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ tt)
... | tri> _ _ p<x  with ∈-ins k x f ⦃ [ p<k ]ᴿ ⦄ rm prfᴿ
  where
    rt⁺ = insertWith k f ⦃ [ p<k ]ᴿ ⦄ rm
    prfᴿ = inᴿ-joinᴿ⁺ x p ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lm rt⁺ bal [ p<x ]ᴿ prf
... | inj₁ prf = inj₁ prf
... | inj₂ prf = inj₂ (right ⦃ [ p<x ]ᴿ ⦄ prf)
∈-ins k x f ⦃ l<k ⦄ (node p lm rm bal) prf | tri< k<x _ _ | tri≈ _ refl _ with prf
... | here x = inj₁ refl
... | left prf = inj₂ (left prf)
... | right prf = inj₂ (right prf)
∈-ins k x f ⦃ l<k ⦄ (node p lm rm bal) prf | tri> _ _ x<k with compare k (proj₁ p)
∈-ins k x f ⦃ l<k ⦄ (node p lm rm bal) prf | tri> _ _ x<k | tri< k<p _ _ with compare x (proj₁ p)
... | tri≈ _ refl _ = inj₂ (here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ tt)
... | tri> _ _ c = inj₂ (right ⦃ [ c ]ᴿ ⦄ prf')
  where
    lt⁺ = insertWith k f ⦃ p≤u = [ k<p ]ᴿ ⦄ lm
    prf' = inᴿ-joinᴸ⁺ x p ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lt⁺ rm bal [ c ]ᴿ prf
... | tri< x<p _ _ with ∈-ins k x f ⦃ k<u = [ k<p ]ᴿ ⦄ lm prf'
  where
    lt⁺ = insertWith k f ⦃ p≤u = [ k<p ]ᴿ ⦄ lm
    prf' = inᴸ-joinᴸ⁺ x p ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lt⁺ rm bal [ x<p ]ᴿ prf
... | inj₁ prf = inj₁ prf
... | inj₂ prf = inj₂ (left ⦃ [ x<p ]ᴿ ⦄ prf)
∈-ins k x f ⦃ l<k ⦄ ⦃ k<u ⦄ (node p lm rm bal) prf | tri> _ _ x<k | tri> _ _ p<k with compare x (proj₁ p)
... | tri< x<p _ _ = inj₂ (left ⦃ [ x<p ]ᴿ ⦄ prf' )
  where
    rt⁺ = insertWith k f ⦃ [ p<k ]ᴿ ⦄ rm
    prf' = inᴸ-joinᴿ⁺ x p ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lm rt⁺ bal [ x<p ]ᴿ prf
... | tri≈ _ refl _ = inj₂ (here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ tt)
... | tri> _ _ p<x with ∈-ins k x f ⦃ [ p<k ]ᴿ ⦄ rm prfᴿ
  where
    rt⁺ = insertWith k f ⦃ [ p<k ]ᴿ ⦄ rm
    prfᴿ = inᴿ-joinᴿ⁺ x p ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lm rt⁺ bal [ p<x ]ᴿ prf
... | inj₁ prf = inj₁ prf
... | inj₂ prf = inj₂ (right ⦃ [ p<x ]ᴿ ⦄ prf)
∈-ins k x f ⦃ l<k ⦄ (node p lm rm bal) prf | tri> _ _ x<k | tri≈ _ refl _ with prf
... | here x = inj₁ refl
... | left prf = inj₂ (left prf)
... | right prf = inj₂ (right prf)

---------------------------------------------------------------------------------
-- ins-comm
---------------------------------------------------------------------------------

ins-comm : ∀ {l u : Key⁺} {h : ℕ}
           (x y z : Key)
           {v : V}
           {{l<x : l <⁺ [ x ]}} {{x<u : [ x ] <⁺ u}}
           {{l<y : l <⁺ [ y ]}} {{y<u : [ y ] <⁺ u}}
           (fˣ fʸ : Maybe V → V)
           (m : BOBMap V l u h)
           → x ≢ y
           → z ↦ v ∈ proj₂ (insertWith x fˣ (proj₂ (insertWith y fʸ m)))
           → z ↦ v ∈ proj₂ (insertWith y fʸ (proj₂ (insertWith x fˣ m)))
ins-comm x y z fˣ fʸ leaf nEq prf with compare x y
... | tri< a ¬b ¬c = {!!}
... | tri≈ ¬a refl ¬c = ⊥-elim (nEq refl)
ins-comm x y z fˣ fʸ leaf nEq prf
  | tri> ¬a ¬b c with compare y x
... | tri< a ¬b₁ ¬c = {!!}
ins-comm x y z fˣ fʸ leaf nEq prf
  | tri> ¬a ¬b c | tri≈ ¬a₁ refl ¬c = ⊥-elim (nEq refl)
ins-comm x y z fˣ fʸ leaf nEq prf
  | tri> ¬a ¬b _ | tri> ¬a₁ ¬b₁ c with prf
... | here α = right ⦃ [ c ]ᴿ ⦄ (here ⦃ [ c ]ᴿ ⦄ ⦃ {!!} ⦄ α)
... | right (here α) = here ⦃ k≤u = {!!} ⦄ α
ins-comm x y z fˣ fʸ (node p lt rt bal) nEq prf = {!!}

-- -}
-- -}
-- -}
-- -}
