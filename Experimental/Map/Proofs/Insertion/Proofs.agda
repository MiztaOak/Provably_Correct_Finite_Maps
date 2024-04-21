{-# OPTIONS --erasure #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet using (OrdSet; toStrictTotalOrder)

module Map.Proofs.Insertion.Proofs {k ℓ₁ v} (order : OrdSet k ℓ₁) (V : Set v) where
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
open import Map.Proofs.Insertion.Helpers order V

---------------------------------------------------------------------------------
-- Induction Principle using insert
---------------------------------------------------------------------------------
∈-singleton : ∀ {l u : Key⁺} {k k' v v'}
  ⦃ l<k' : l <⁺ [ k' ] ⦄ ⦃ k'<u : [ k' ] <⁺ u ⦄
  → k ↦ v ∈ singleton k' v' → k ≡ k' × v ≡ v'
∈-singleton (here x) = refl , x

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
-- Prove that Insert results in ∈
---------------------------------------------------------------------------------
insert∈ : ∀ {l u : Key⁺} {h : ℕ} (k : Key) (v : V)
          {{@erased l<k : l <⁺ [ k ]}} {{@erased k<u : [ k ] <⁺ u}}
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
        {v : V}
        (f : Maybe V → V)
        {{@erased l<k : l <⁺ [ k ]}} {{@erased k<u : [ k ] <⁺ u}}
        (m : BOBMap V l u h)
        → x ↦ v ∈ proj₂ (insertWith k f m)
        → (x ≡ k) ⊎ x ↦ v ∈ m
∈-ins k .k f leaf (here x) = inj₁ refl
∈-ins k x f ⦃ l<k ⦄ (node p lm rm bal) prf with compare k x
... | tri≈ _ refl _ = inj₁ refl
∈-ins k x f ⦃ l<k ⦄ (node p lm rm bal) prf | tri< k<x _ _ with compare k (proj₁ p)
∈-ins k x f ⦃ l<k ⦄ (node p lm rm bal) prf | tri< k<x _ _ | tri< k<p _ _ with compare x (proj₁ p)
... | tri≈ _ refl _ = inj₂ (here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ (inC-joinᴸ⁺ lm⁺ rm bal prf))
  where
    lm⁺ = insertWith k f ⦃ p≤u = [ k<p ]ᴿ ⦄ lm
... | tri> _ _ c = inj₂ (right ⦃ [ c ]ᴿ ⦄ (inᴿ-joinᴸ⁺ ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lm⁺ rm bal [ c ]ᴿ prf))
  where
    lm⁺ = insertWith k f ⦃ p≤u = [ k<p ]ᴿ ⦄ lm
... | tri< x<p _ _ with ∈-ins k x f ⦃ k<u = [ k<p ]ᴿ ⦄ lm prf'
  where
    lt⁺ = insertWith k f ⦃ p≤u = [ k<p ]ᴿ ⦄ lm
    prf' = inᴸ-joinᴸ⁺ ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lt⁺ rm bal [ x<p ]ᴿ prf
... | inj₁ prf = inj₁ prf
... | inj₂ prf = inj₂ (left ⦃ [ x<p ]ᴿ ⦄ prf)
∈-ins k x f ⦃ l<k ⦄ ⦃ k<u ⦄ (node p lm rm bal) prf | tri< k<x _ _ | tri> _ _ p<k with compare x (proj₁ p)
... | tri< a _ _ = inj₂ (left ⦃ [ a ]ᴿ ⦄ (inᴸ-joinᴿ⁺ ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lm rt⁺ bal [ a ]ᴿ prf))
  where
    rt⁺ = insertWith k f ⦃ [ p<k ]ᴿ ⦄ rm
... | tri≈ _ refl _ = inj₂ (here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ (inC-joinᴿ⁺ lm rm⁺ bal prf))
  where
    rm⁺ = insertWith k f ⦃ [ p<k ]ᴿ ⦄ rm
... | tri> _ _ p<x  with ∈-ins k x f ⦃ [ p<k ]ᴿ ⦄ rm prfᴿ
  where
    rt⁺ = insertWith k f ⦃ [ p<k ]ᴿ ⦄ rm
    prfᴿ = inᴿ-joinᴿ⁺ ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lm rt⁺ bal [ p<x ]ᴿ prf
... | inj₁ prf = inj₁ prf
... | inj₂ prf = inj₂ (right ⦃ [ p<x ]ᴿ ⦄ prf)
∈-ins k x f ⦃ l<k ⦄ (node p lm rm bal) prf | tri< k<x _ _ | tri≈ _ refl _ with prf
... | here x = inj₁ refl
... | left prf = inj₂ (left prf)
... | right prf = inj₂ (right prf)
∈-ins k x f ⦃ l<k ⦄ (node p lm rm bal) prf | tri> _ _ x<k with compare k (proj₁ p)
∈-ins k x f ⦃ l<k ⦄ (node p lm rm bal) prf | tri> _ _ x<k | tri< k<p _ _ with compare x (proj₁ p)
... | tri≈ _ refl _ = inj₂ (here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ (inC-joinᴸ⁺ lm⁺ rm bal prf))
  where
    lm⁺ = insertWith k f ⦃ p≤u = [ k<p ]ᴿ ⦄ lm
... | tri> _ _ c = inj₂ (right ⦃ [ c ]ᴿ ⦄ prf')
  where
    lt⁺ = insertWith k f ⦃ p≤u = [ k<p ]ᴿ ⦄ lm
    prf' = inᴿ-joinᴸ⁺ ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lt⁺ rm bal [ c ]ᴿ prf
... | tri< x<p _ _ with ∈-ins k x f ⦃ k<u = [ k<p ]ᴿ ⦄ lm prf'
  where
    lt⁺ = insertWith k f ⦃ p≤u = [ k<p ]ᴿ ⦄ lm
    prf' = inᴸ-joinᴸ⁺ ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lt⁺ rm bal [ x<p ]ᴿ prf
... | inj₁ prf = inj₁ prf
... | inj₂ prf = inj₂ (left ⦃ [ x<p ]ᴿ ⦄ prf)
∈-ins k x f ⦃ l<k ⦄ ⦃ k<u ⦄ (node p lm rm bal) prf | tri> _ _ x<k | tri> _ _ p<k with compare x (proj₁ p)
... | tri< x<p _ _ = inj₂ (left ⦃ [ x<p ]ᴿ ⦄ prf' )
  where
    rt⁺ = insertWith k f ⦃ [ p<k ]ᴿ ⦄ rm
    prf' = inᴸ-joinᴿ⁺ ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lm rt⁺ bal [ x<p ]ᴿ prf
... | tri≈ _ refl _ = inj₂ (here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ (inC-joinᴿ⁺ lm rm⁺ bal prf))
  where
    rm⁺ = insertWith k f ⦃ [ p<k ]ᴿ ⦄ rm
... | tri> _ _ p<x with ∈-ins k x f ⦃ [ p<k ]ᴿ ⦄ rm prfᴿ
  where
    rt⁺ = insertWith k f ⦃ [ p<k ]ᴿ ⦄ rm
    prfᴿ = inᴿ-joinᴿ⁺ ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lm rt⁺ bal [ p<x ]ᴿ prf
... | inj₁ prf = inj₁ prf
... | inj₂ prf = inj₂ (right ⦃ [ p<x ]ᴿ ⦄ prf)
∈-ins k x f ⦃ l<k ⦄ (node p lm rm bal) prf | tri> _ _ x<k | tri≈ _ refl _ with prf
... | here x = inj₁ refl
... | left prf = inj₂ (left prf)
... | right prf = inj₂ (right prf)

insEq : ∀ {l u : Key⁺} {h : ℕ}
        (x : Key)
        {v v' : V}
        {{@erased l<k : l <⁺ [ x ]}} {{@erased k<u : [ x ] <⁺ u}}
        (m : BOBMap V l u h)
        → x ↦ v ∈ proj₂ (insert (x , v') m)
        → v ≡ v'
insEq x leaf (here refl) = refl
insEq x (node p lt rt bal) prf with compare x (proj₁ p)
insEq x {v' = v'} (node p lt rt bal) prf | tri< x<p _ _ = insEq x ⦃ k<u = [ x<p ]ᴿ ⦄ lt prf'
  where
    lt⁺ = insert (x , v') ⦃ p≤u = [ x<p ]ᴿ ⦄ lt
    prf' = inᴸ-joinᴸ⁺ ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ lt⁺ rt bal [ x<p ]ᴿ prf
insEq x (node p lt rt bal) prf | tri≈ _ refl _ with prf
... | here refl = refl
... | left ⦃ ord ⦄ _ = ⊥-elim (irrefl⁺ [ proj₁ p ] ord)
... | right ⦃ ord ⦄ _ = ⊥-elim (irrefl⁺ [ proj₁ p ] ord)
insEq x {v' = v'} (node p lt rt bal) prf | tri> _ _ p<x = insEq x ⦃ [ p<x ]ᴿ ⦄ rt prf'
  where
    rt⁺ = insert (x , v') ⦃ [ p<x ]ᴿ ⦄ rt
    prf' = inᴿ-joinᴿ⁺ ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ lt rt⁺ bal [ p<x ]ᴿ prf

---------------------------------------------------------------------------------
-- ins-comm
---------------------------------------------------------------------------------
isEq? : ∀ (x y : Key) → x ≡ y ⊎ x ≢ y
isEq? x y with compare x y
... | tri< _ nEq _  = inj₂ nEq
... | tri≈ _ refl _ = inj₁ refl
... | tri> _ nEq _  = inj₂ nEq

insert-joinR→R : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (x y z : Key)
    (p : Key × V)
    (v vˣ vʸ : V)
    ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ p<x : [ proj₁ p ] <⁺ [ x ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
    ⦃ l<y : l <⁺ [ y ] ⦄ ⦃ p<y : [ proj₁ p ] <⁺ [ y ] ⦄ ⦃ y<u : [ y ] <⁺ u ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → x ≢ y
    → z ↦ v ∈ (proj₂ (insert (x , vˣ) (proj₂ (joinʳ⁺ p lt (insert (y , vʸ) rt) bal))))
    → z ↦ v ∈ (proj₂ (insert (y , vʸ) (proj₂ (joinʳ⁺ p lt (insert (x , vˣ) rt) bal))))
insert-joinR→R x y z p v vˣ vʸ ⦃ p<x = p<x ⦄ lt rt bal nEq prf with insert (y , vʸ) rt in insYEq
... | rtʸ with joinʳ⁺ p lt rtʸ bal in jEq
... | rt⁺ with ∈-ins x z (λ _ → vˣ) (proj₂ rt⁺) prf
... | inj₁ refl rewrite insEq x (proj₂ rt⁺) prf = insert-safe prfJoin nEq
  where
    m = insert (x , vˣ) rt
    prfIns = insert∈ x vˣ rt
    prfJoin = anyᴿjoinᴿ⁺ lt m bal p<x prfIns
insert-joinR→R x y z p v vˣ vʸ lt rt bal nEq prf | rtʸ | (i , rt⁺) | inj₂ prfᴿ with jEq
... | refl with compare z (proj₁ p)
insert-joinR→R x y z p v vˣ vʸ ⦃ p<y = p<y ⦄ lt rt bal nEq prf
  | rtʸ | (i , rt⁺) | inj₂ prfᴿ | refl | tri< z<p _ _ with isEq? z y
... | inj₁ refl = ⊥-elim (asym z<p [ p<y ]-lower)
... | inj₂ z≢y = insert-safe prfJoin z≢y
  where
    prfᴸ = inᴸ-joinᴿ⁺ ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ lt rtʸ bal [ z<p ]ᴿ prfᴿ
    m = insertWith x (λ _ → vˣ) rt
    prfJoin = anyᴸjoinᴿ⁺ lt m bal [ z<p ]ᴿ prfᴸ
insert-joinR→R x y z p v vˣ vʸ ⦃ p<y = p<y ⦄ lt rt bal nEq prf
  | rtʸ | (i , rt⁺) | inj₂ prfᴿ | refl | tri≈ _ refl _ rewrite inC-joinᴿ⁺ lt rtʸ bal prfᴿ with isEq? z y
... | inj₁ refl = ⊥-elim (irrefl⁺ [ proj₁ p ] p<y)
... | inj₂ z≢y = insert-safe prfJoin z≢y
  where
    prfJoin = herejoinᴿ⁺ lt (insert (x , vˣ) rt) bal
insert-joinR→R x y z p v vˣ vʸ lt rt bal nEq prf
  | rtʸ | (i , rt⁺) | inj₂ prfᴿ | refl | tri> _ _ p<z with insYEq
... | refl with inᴿ-joinᴿ⁺ ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ lt rtʸ bal [ p<z ]ᴿ prfᴿ
... | prfIns with ∈-ins y z (λ _ → vʸ) rt prfIns
... | inj₁ refl rewrite insEq y rt prfIns = insert∈ y vʸ m
  where
    m = proj₂ (joinʳ⁺ p lt (insertWith x (λ _ → vˣ) rt) bal)
... | inj₂ prfᴿ' with isEq? z x
... | inj₁ refl rewrite insEq z (proj₂ (joinʳ⁺ p lt (insertWith y (λ _ → vʸ) rt) bal)) prf = res
  where
    prfInsX = insert∈ x vˣ rt
    prfJoin = anyᴿjoinᴿ⁺ lt (insert (z , vˣ) rt) bal [ p<z ]ᴿ prfInsX
    res = insert-safe prfJoin nEq
... | inj₂ z≢x with isEq? z y
... | inj₂ z≢y = insert-safe prfJoin z≢y
  where
    prfInsX = insert-safe prfᴿ' z≢x
    prfJoin = anyᴿjoinᴿ⁺ lt (insert (x , vˣ) rt) bal [ p<z ]ᴿ prfInsX
... | inj₁ refl rewrite insEq z rt prfIns = insert∈ z vʸ m
  where
    m = (proj₂ (joinʳ⁺ p lt (insertWith x (λ _ → vˣ) rt) bal))

insert-joinL→L : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (x y z : Key)
    (p : Key × V)
    (v vˣ vʸ : V)
    ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ x<p : [ x ] <⁺ [ proj₁ p ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
    ⦃ l<y : l <⁺ [ y ] ⦄ ⦃ y<p : [ y ] <⁺ [ proj₁ p ] ⦄ ⦃ y<u : [ y ] <⁺ u ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → x ≢ y
    → z ↦ v ∈ (proj₂ (insert (x , vˣ) (proj₂ (joinˡ⁺ p (insert (y , vʸ) lt) rt bal))))
    → z ↦ v ∈ (proj₂ (insert (y , vʸ) (proj₂ (joinˡ⁺ p (insert (x , vˣ) lt) rt bal))))
insert-joinL→L x y z p v vˣ vʸ ⦃ x<p = x<p ⦄ lt rt bal nEq prf with insert (y , vʸ) lt in insYEq
... | ltʸ with joinˡ⁺ p ltʸ rt bal in jEq
... | lt⁺ with ∈-ins x z (λ _ → vˣ) (proj₂ lt⁺) prf
... | inj₁ refl rewrite insEq x (proj₂ lt⁺) prf = insert-safe prfJoin nEq
  where
    prfIns = insert∈ x vˣ lt
    prfJoin = anyᴸjoinᴸ⁺ (insert (x , vˣ) lt) rt bal x<p prfIns
insert-joinL→L x y z p v vˣ vʸ lt rt bal nEq prf | ltʸ | lt⁺ | inj₂ prfᴸ with jEq
... | refl with compare z (proj₁ p)
insert-joinL→L x y z p v vˣ vʸ lt rt bal nEq prf
  | ltʸ | lt⁺ | inj₂ prfᴸ | refl | tri< z<p _ _ with insYEq
... | refl with inᴸ-joinᴸ⁺ ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ ltʸ rt bal [ z<p ]ᴿ prfᴸ
... | prfIns with ∈-ins y z (λ _ → vʸ) lt prfIns
... | inj₁ refl rewrite insEq y lt prfIns = insert∈ y vʸ m
  where
    m = proj₂ (joinˡ⁺ p (insertWith x (λ _ → vˣ) lt) rt bal)
... | inj₂ prfᴸ' with isEq? z x
... | inj₁ refl rewrite insEq x (proj₂ lt⁺) prf = insert-safe prfJoin nEq
  where
    prfInsX = insert∈ x vˣ lt
    prfJoin = anyᴸjoinᴸ⁺ (insert (x , vˣ) lt) rt bal [ z<p ]ᴿ prfInsX
... | inj₂ z≢x with isEq? z y
... | inj₁ refl rewrite insEq y lt prfIns = insert∈ y vʸ m
  where
    m = proj₂ (joinˡ⁺ p (insertWith x (λ _ → vˣ) lt) rt bal)
... | inj₂ z≢y = insert-safe prfJoin z≢y
  where
    prfInsX = insert-safe prfᴸ' z≢x
    prfJoin = anyᴸjoinᴸ⁺ (insert (x , vˣ) lt) rt bal [ z<p ]ᴿ prfInsX
insert-joinL→L x y z p v vˣ vʸ ⦃ y<p = y<p ⦄ lt rt bal nEq prf
  | ltʸ | lt⁺ | inj₂ prfᴸ | refl | tri≈ _ refl _ rewrite inC-joinᴸ⁺ ltʸ rt bal prfᴸ with isEq? z y
... | inj₁ refl = ⊥-elim (irrefl⁺ [ y ] y<p)
... | inj₂ z≢y = insert-safe prfJoin z≢y
  where
    prfJoin = herejoinᴸ⁺ (insert (x , vˣ) lt) rt bal
insert-joinL→L x y z p v vˣ vʸ ⦃ y<p = z<p ⦄ lt rt bal nEq prf
  | ltʸ | lt⁺ | inj₂ prfᴸ | refl | tri> !z<p _ p<z with isEq? z y
... | inj₁ refl = ⊥-elim (!z<p [ z<p ]-lower)
... | inj₂ z≢y = insert-safe prfJoin z≢y
  where
    prfᴿ = inᴿ-joinᴸ⁺ ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ ltʸ rt bal [ p<z ]ᴿ prfᴸ
    prfJoin = anyᴿjoinᴸ⁺ (insert (x , vˣ) lt) rt bal [ p<z ]ᴿ prfᴿ

insert-joinL→R : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (x y z : Key)
    (p : Key × V)
    (v vˣ vʸ : V)
    ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ p<x : [ proj₁ p ] <⁺ [ x ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
    ⦃ l<y : l <⁺ [ y ] ⦄ ⦃ y<p : [ y ] <⁺ [ proj₁ p ] ⦄ ⦃ y<u : [ y ] <⁺ u ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → x ≢ y
    → z ↦ v ∈ (proj₂ (insert (x , vˣ) (proj₂ (joinˡ⁺ p (insert (y , vʸ) lt) rt bal))))
    → z ↦ v ∈ (proj₂ (insert (y , vʸ) (proj₂ (joinʳ⁺ p lt (insert (x , vˣ) rt) bal))))
insert-joinL→R x y z p v vˣ vʸ ⦃ p<x = p<x ⦄ lt rt bal nEq prf with insert (y , vʸ) lt in insYEq
... | ltʸ with joinˡ⁺ p ltʸ rt bal in jEq
... | lt⁺ with ∈-ins x z (λ _ → vˣ) (proj₂ lt⁺) prf
... | inj₁ refl rewrite insEq x (proj₂ lt⁺) prf = insert-safe prfJoin nEq
  where
    prfIns = insert∈ x vˣ rt
    prfJoin = anyᴿjoinᴿ⁺ lt (insert (x , vˣ) rt) bal p<x prfIns
insert-joinL→R x y z p v vˣ vʸ lt rt bal nEq prf | ltʸ | lt⁺ | inj₂ prfᴸ with jEq
... | refl with compare z (proj₁ p)
insert-joinL→R x y z p v vˣ vʸ lt rt bal nEq prf
  | ltʸ | lt⁺ | inj₂ prfᴸ | refl | tri< z<p _ _ with insYEq
... | refl with inᴸ-joinᴸ⁺ ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ ltʸ rt bal [ z<p ]ᴿ prfᴸ
... | prfIns with ∈-ins y z (λ _ → vʸ) lt prfIns
... | inj₁ refl rewrite insEq y lt prfIns = insert∈ y vʸ m
  where
    m = proj₂ (joinʳ⁺ p lt (insertWith x (λ _ → vˣ) rt) bal)
... | inj₂ prfᴸ' with isEq? z y
... | inj₁ refl rewrite insEq y lt prfIns = insert∈ y vʸ m
  where
    m = proj₂ (joinʳ⁺ p lt (insertWith x (λ _ → vˣ) rt) bal)
... | inj₂ z≢y = insert-safe prfJoin z≢y
  where
    prfJoin = anyᴸjoinᴿ⁺ lt (insert (x , vˣ) rt) bal [ z<p ]ᴿ prfᴸ'
insert-joinL→R x y z p v vˣ vʸ ⦃ y<p = p<p ⦄ lt rt bal nEq prf
  | ltʸ | lt⁺ | inj₂ prfᴸ | refl | tri≈ p≮p refl _ rewrite inC-joinᴸ⁺ ltʸ rt bal prfᴸ with isEq? z y
... | inj₁ refl = ⊥-elim (p≮p [ p<p ]-lower)
... | inj₂ z≢y = insert-safe prfJoin z≢y
  where
    prfJoin = herejoinᴿ⁺ lt (insert (x , vˣ) rt) bal
insert-joinL→R x y z p v vˣ vʸ ⦃ y<p = z<p ⦄ lt rt bal nEq prf
  | ltʸ | lt⁺ | inj₂ prfᴸ | refl | tri> z≮p _ p<z with isEq? z y
... | inj₁ refl = ⊥-elim (z≮p [ z<p ]-lower)
... | inj₂ z≢y with isEq? z x
... | inj₁ refl rewrite insEq x (proj₂ (joinˡ⁺ p ltʸ rt bal)) prf = insert-safe prfJoin z≢y
  where
    prfInsX = insert∈ x vˣ rt
    prfJoin = anyᴿjoinᴿ⁺ lt (insert (x , vˣ) rt) bal [ p<z ]ᴿ prfInsX
... | inj₂ z≢x = insert-safe prfJoin z≢y
  where
    prfᴿ = inᴿ-joinᴸ⁺ ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ ltʸ rt bal [ p<z ]ᴿ prfᴸ
    prfInsX = insert-safe prfᴿ z≢x
    prfJoin = anyᴿjoinᴿ⁺ lt (insert (x , vˣ) rt) bal [ p<z ]ᴿ prfInsX

insert-joinR→L : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (x y z : Key)
    (p : Key × V)
    (v vˣ vʸ : V)
    ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ x<p : [ x ] <⁺ [ proj₁ p ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
    ⦃ l<y : l <⁺ [ y ] ⦄ ⦃ p<y : [ proj₁ p ] <⁺ [ y ] ⦄ ⦃ y<u : [ y ] <⁺ u ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → x ≢ y
    → z ↦ v ∈ (proj₂ (insert (x , vˣ) (proj₂ (joinʳ⁺ p lt (insert (y , vʸ) rt) bal))))
    → z ↦ v ∈ (proj₂ (insert (y , vʸ) (proj₂ (joinˡ⁺ p (insert (x , vˣ) lt) rt bal))))
insert-joinR→L x y z p v vˣ vʸ ⦃ x<p = x<p ⦄ lt rt bal nEq prf with insert (y , vʸ) rt in insYEq
... | rtʸ with joinʳ⁺ p lt rtʸ bal in jEq
... | rt⁺ with ∈-ins x z (λ _ → vˣ) (proj₂ rt⁺) prf
... | inj₁ refl rewrite insEq x (proj₂ rt⁺) prf = insert-safe prfJoin nEq
  where
    prfIns = insert∈ x vˣ lt
    prfJoin = anyᴸjoinᴸ⁺ (insert (x , vˣ) lt) rt bal x<p prfIns
insert-joinR→L x y z p v vˣ vʸ lt rt bal nEq prf | rtʸ | rt⁺ | inj₂ prfᴿ with jEq
... | refl with compare z (proj₁ p)
insert-joinR→L x y z p v vˣ vʸ ⦃ p<y = p<z ⦄ lt rt bal nEq prf
  | rtʸ | rt⁺ | inj₂ prfᴿ | refl | tri< z<p _ p≮z with isEq? z y
... | inj₁ refl = ⊥-elim (p≮z [ p<z ]-lower)
... | inj₂ z≢y with isEq? z x
... | inj₁ refl rewrite insEq x (proj₂ (joinʳ⁺ p lt rtʸ bal)) prf = insert-safe prfJoin z≢y
  where
    prfInsX = insert∈ x vˣ lt
    prfJoin = anyᴸjoinᴸ⁺ (insert (x , vˣ) lt) rt bal [ z<p ]ᴿ prfInsX
... | inj₂ z≢x = insert-safe prfJoin z≢y
  where
    prfᴸ = inᴸ-joinᴿ⁺ ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ lt rtʸ bal [ z<p ]ᴿ prfᴿ
    prfInsX = insert-safe prfᴸ z≢x
    prfJoin = anyᴸjoinᴸ⁺ (insert (x , vˣ) lt) rt bal [ z<p ]ᴿ prfInsX
insert-joinR→L x y z p v vˣ vʸ ⦃ p<y = p<p ⦄ lt rt bal nEq prf
  | rtʸ | rt⁺ | inj₂ prfᴿ | refl | tri≈ p≮p refl _ rewrite inC-joinᴿ⁺ lt rtʸ bal prfᴿ with isEq? z y
... | inj₁ refl = ⊥-elim (p≮p [ p<p ]-lower)
... | inj₂ z≢y = insert-safe prfJoin z≢y
  where
    prfJoin = herejoinᴸ⁺ (insert (x , vˣ) lt) rt bal
insert-joinR→L x y z p v vˣ vʸ lt rt bal nEq prf
  | rtʸ | rt⁺ | inj₂ prfᴿ | refl | tri> _ _ p<z with insYEq
... | refl with inᴿ-joinᴿ⁺ ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ lt rtʸ bal [ p<z ]ᴿ prfᴿ
... | prfIns with ∈-ins y z (λ _ → vʸ) rt prfIns
... | inj₁ refl rewrite insEq y rt prfIns = insert∈ y vʸ m
  where
    m = proj₂ (joinˡ⁺ p (insertWith x (λ _ → vˣ) lt) rt bal)
... | inj₂ prfᴿ' with isEq? z y
... | inj₁ refl rewrite insEq y rt prfIns = insert∈ y vʸ m
  where
    m = proj₂ (joinˡ⁺ p (insertWith x (λ _ → vˣ) lt) rt bal)
... | inj₂ z≢y = insert-safe prfJoin z≢y
  where
    prfJoin = anyᴿjoinᴸ⁺ (insert (x , vˣ) lt) rt bal [ p<z ]ᴿ prfᴿ'

insert-joinL : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (y z : Key)
    (p : Key × V)
    (v vˣ vʸ : V)
    ⦃ l<x : l <⁺ [ proj₁ p ] ⦄ ⦃ x<u : [ proj₁ p ] <⁺ u ⦄
    ⦃ l<y : l <⁺ [ y ] ⦄ ⦃ y<p : [ y ] <⁺ [ proj₁ p ] ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → (proj₁ p) ≢ y
    → z ↦ v ∈ (proj₂ (insert (proj₁ p , vˣ) (proj₂ (joinˡ⁺ p (insert (y , vʸ) lt) rt bal))))
    → z ↦ v ∈ (proj₂ (joinˡ⁺ (proj₁ p , vˣ) (insert (y , vʸ) lt) rt bal))
insert-joinL y z p v vˣ vʸ lt rt bal nEq prf with ∈-ins (proj₁ p) z (λ _ → vˣ) m prf
  where
    m = proj₂ (joinˡ⁺ p (insert (y , vʸ) lt) rt bal)
... | inj₁ refl rewrite insEq (proj₁ p) (proj₂ (joinˡ⁺ p (insert (y , vʸ) lt) rt bal)) prf =
  herejoinᴸ⁺ (insert (y , vʸ) lt) rt bal
... | inj₂ prf' with compare z (proj₁ p)
... | tri< z<p _ _ = anyᴸjoinᴸ⁺ (insert (y , vʸ) lt) rt bal [ z<p ]ᴿ prfᴸ
  where
    prfᴸ = inᴸ-joinᴸ⁺ (insert (y , vʸ) lt) rt bal [ z<p ]ᴿ prf'
... | tri≈ _ refl _ rewrite insEq (proj₁ p) (proj₂ (joinˡ⁺ p (insertWith y (λ _ → vʸ) lt) rt bal)) prf =
  herejoinᴸ⁺ (insert (y , vʸ) lt) rt bal
... | tri> _ _ p<z = anyᴿjoinᴸ⁺ (insert (y , vʸ) lt) rt bal [ p<z ]ᴿ prfᴿ
  where
    prfᴿ = inᴿ-joinᴸ⁺ (insert (y , vʸ) lt) rt bal [ p<z ]ᴿ prf'

insert-joinR : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (y z : Key)
    (p : Key × V)
    (v vˣ vʸ : V)
    ⦃ l<x : l <⁺ [ proj₁ p ] ⦄ ⦃ x<u : [ proj₁ p ] <⁺ u ⦄
    ⦃ p<y : [ proj₁ p ] <⁺ [ y ] ⦄ ⦃ y<u : [ y ] <⁺ u ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → (proj₁ p) ≢ y
    → z ↦ v ∈ (proj₂ (insert (proj₁ p , vˣ) (proj₂ (joinʳ⁺ p lt (insert (y , vʸ) rt) bal))))
    → z ↦ v ∈ (proj₂ (joinʳ⁺ (proj₁ p , vˣ) lt (insert (y , vʸ) rt) bal))
insert-joinR y z p v vˣ vʸ lt rt bal nEq prf with joinʳ⁺ p lt (insert (y , vʸ) rt) bal in joinEq
... | rt⁺ with ∈-ins (proj₁ p) z (λ _ → vˣ) (proj₂ rt⁺) prf
... | inj₁ refl rewrite insEq (proj₁ p) (proj₂ rt⁺) prf = herejoinᴿ⁺ lt (insert (y , vʸ) rt) bal
... | inj₂ prfᴿ with joinEq
... | refl with compare z (proj₁ p)
... | tri< z<p _ _ = anyᴸjoinᴿ⁺ lt (insert (y , vʸ) rt) bal [ z<p ]ᴿ prfᴸ
  where
    prfᴸ = inᴸ-joinᴿ⁺ lt (insert (y , vʸ) rt) bal [ z<p ]ᴿ prfᴿ
... | tri≈ _ refl _ rewrite insEq (proj₁ p) (proj₂ rt⁺) prf = herejoinᴿ⁺ lt (insert (y , vʸ) rt) bal
... | tri> _ _ p<z = anyᴿjoinᴿ⁺ lt (insert (y , vʸ) rt) bal [ p<z ]ᴿ prfᴿ'
  where
    prfᴿ' = inᴿ-joinᴿ⁺ lt (insert (y , vʸ) rt) bal [ p<z ]ᴿ prfᴿ

insert-comm : ∀ {l u : Key⁺} {h : ℕ}
           (x y z : Key)
           {v : V}
           {{l<x : l <⁺ [ x ]}} {{x<u : [ x ] <⁺ u}}
           {{l<y : l <⁺ [ y ]}} {{y<u : [ y ] <⁺ u}}
           (vˣ vʸ : V)
           (m : BOBMap V l u h)
           → x ≢ y
           → z ↦ v ∈ proj₂ (insert (x , vˣ) (proj₂ (insert (y , vʸ) m)))
           → z ↦ v ∈ proj₂ (insert (y , vʸ) (proj₂ (insert (x , vˣ) m)))
---- leaf cases ----
insert-comm x y z ⦃ y<u = y<u ⦄ vˣ vʸ leaf nEq prf with compare x y
... | tri< x<y  _ _ with compare y x
... | tri< _ _ ¬x<y = ⊥-elim (¬x<y x<y)
... | tri≈ _ refl _ = ⊥-elim (nEq refl)
... | tri> _ _ _  with prf
... | here α = right ⦃ [ x<y ]ᴿ ⦄ (here ⦃ [ x<y ]ᴿ ⦄ ⦃ y<u ⦄ α)
... | left (here ⦃ l<x ⦄ α) = here ⦃ l<x ⦄ α
insert-comm x y z vˣ vʸ leaf nEq prf | tri≈ _ refl _ = ⊥-elim (nEq refl)
insert-comm x y z ⦃ l<y = l<y ⦄ vˣ vʸ leaf nEq prf | tri> _ _ y<x with compare y x
... | tri< _ _ _ with prf
... | here α = left ⦃ [ y<x ]ᴿ ⦄ (here ⦃ l<y ⦄ ⦃ [ y<x ]ᴿ ⦄ α)
... | right (here ⦃ k≤u = x<u ⦄ α) = here ⦃ k≤u = x<u ⦄ α
insert-comm x y z vˣ vʸ leaf nEq prf | tri> _ _ y<x | tri≈ _ refl _ = ⊥-elim (nEq refl)
insert-comm x y z ⦃ x<u = x<u ⦄ ⦃ y<u = y<u ⦄ vˣ vʸ leaf nEq prf | tri> _ _ y<x | tri> _ _ c with prf
... | here α = right ⦃ [ c ]ᴿ ⦄ (here ⦃ [ c ]ᴿ ⦄ ⦃ y<u ⦄ α)
... | right (here α) = here ⦃ k≤u = x<u ⦄ α
---- node cases ----
insert-comm x y z {v} vˣ vʸ (node p lt rt bal) nEq prf with compare y (proj₁ p) in compY
... | tri< y<p _ _ with compare x (proj₁ p)
... | tri< x<p _ _ = insert-joinL→L x y z p v vˣ vʸ ⦃ x<p = [ x<p ]ᴿ ⦄ ⦃ y<p = [ y<p ]ᴿ ⦄ lt rt bal nEq prf
... | tri≈ _ refl _ rewrite compY = insert-joinL y z p v vˣ vʸ ⦃ y<p = [ y<p ]ᴿ ⦄ lt rt bal nEq prf
... | tri> _ _ p<x = insert-joinL→R x y z p v vˣ vʸ ⦃ p<x = [ p<x ]ᴿ ⦄ ⦃ y<p = [ y<p ]ᴿ ⦄ lt rt bal nEq prf
insert-comm x y z {v} vˣ vʸ (node p lt rt bal) nEq prf | tri≈ _ refl _ with compare x (proj₁ p)
... | tri≈ _ refl _ rewrite compY = ⊥-elim (nEq refl)
... | tri< x<p _ _ with insert (x , vˣ) ⦃ p≤u = [ x<p ]ᴿ ⦄ lt in insX
... | (i , lt') with compare z (proj₁ p)
... | tri< z<p z≢p _ = insert-safe prf'' z≢p
  where
    prf' = inᴸ-joinᴸ⁺ (i , lt') rt bal [ z<p ]ᴿ prf
    prf'' = anyᴸjoinᴸ⁺ (i , lt') rt bal [ z<p ]ᴿ prf'
... | tri≈ _ refl _ rewrite inC-joinᴸ⁺ (i , lt') rt bal prf = insert∈ (proj₁ p) vʸ (proj₂ m')
  where
    m' = joinˡ⁺ p (i , lt') rt bal
... | tri> _ z≢p p<z = insert-safe prf'' z≢p
  where
    prf' = inᴿ-joinᴸ⁺ (i , lt') rt bal [ p<z ]ᴿ prf
    prf'' = anyᴿjoinᴸ⁺ (i , lt') rt bal [ p<z ]ᴿ prf'
insert-comm x y z {v} vˣ vʸ (node p lt rt bal) nEq prf | tri≈ _ refl _ | tri> _ _ p<x with
  insert (x , vˣ) ⦃ [ p<x ]ᴿ ⦄ rt in insX
... | (i , rt') with compare z (proj₁ p)
... | tri< z<p z≢p _ = insert-safe prf'' z≢p
  where
    prf' = inᴸ-joinᴿ⁺ lt (i , rt') bal [ z<p ]ᴿ prf
    prf'' = anyᴸjoinᴿ⁺ lt (i , rt') bal [ z<p ]ᴿ prf'
... | tri≈ _ refl _ rewrite inC-joinᴿ⁺ lt (i , rt') bal prf = insert∈ (proj₁ p) vʸ (proj₂ m')
  where
    m' = joinʳ⁺ p lt (i , rt') bal
... | tri> _ p≢z p<z = insert-safe prf'' p≢z
  where
    prf' = inᴿ-joinᴿ⁺ lt (i , rt') bal [ p<z ]ᴿ prf
    prf'' = anyᴿjoinᴿ⁺ lt (i , rt') bal [ p<z ]ᴿ prf'
insert-comm x y z {v} vˣ vʸ (node p lt rt bal) nEq prf | tri> _ _ p<y with compare x (proj₁ p) in compX
... | tri< x<p _ _ = insert-joinR→L x y z p v vˣ vʸ ⦃ x<p = [ x<p ]ᴿ ⦄ ⦃ p<y = [ p<y ]ᴿ ⦄ lt rt bal nEq prf
... | tri≈ _ refl _ rewrite compY = insert-joinR y z p v vˣ vʸ ⦃ p<y = [ p<y ]ᴿ ⦄ lt rt bal nEq prf
... | tri> _ _ p<x = insert-joinR→R x y z p v vˣ vʸ ⦃ p<x = [ p<x ]ᴿ ⦄ ⦃ p<y = [ p<y ]ᴿ ⦄ lt rt bal nEq prf

postulate
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
{-
---- leaf cases ----
ins-comm x y z ⦃ y<u = y<u ⦄ fˣ fʸ leaf nEq prf with compare x y
... | tri< x<y  _ _ with compare y x
... | tri< _ _ ¬x<y = ⊥-elim (¬x<y x<y)
... | tri≈ _ refl _ = ⊥-elim (nEq refl)
... | tri> _ _ _  with prf
... | here α = right ⦃ [ x<y ]ᴿ ⦄ (here ⦃ [ x<y ]ᴿ ⦄ ⦃ y<u ⦄ α)
... | left (here ⦃ l<x ⦄ α) = here ⦃ l<x ⦄ α
ins-comm x y z fˣ fʸ leaf nEq prf | tri≈ _ refl _ = ⊥-elim (nEq refl)
ins-comm x y z ⦃ l<y = l<y ⦄ fˣ fʸ leaf nEq prf | tri> _ _ y<x with compare y x
... | tri< _ _ _ with prf
... | here α = left ⦃ [ y<x ]ᴿ ⦄ (here ⦃ l<y ⦄ ⦃ [ y<x ]ᴿ ⦄ α)
... | right (here ⦃ k≤u = x<u ⦄ α) = here ⦃ k≤u = x<u ⦄ α
ins-comm x y z fˣ fʸ leaf nEq prf | tri> _ _ y<x | tri≈ _ refl _ = ⊥-elim (nEq refl)
ins-comm x y z ⦃ x<u = x<u ⦄ ⦃ y<u = y<u ⦄ fˣ fʸ leaf nEq prf | tri> _ _ y<x | tri> _ _ c with prf
... | here α = right ⦃ [ c ]ᴿ ⦄ (here ⦃ [ c ]ᴿ ⦄ ⦃ y<u ⦄ α)
... | right (here α) = here ⦃ k≤u = x<u ⦄ α
---- node cases ----
ins-comm x y z fˣ fʸ (node p lt rt bal) nEq prf with compare y (proj₁ p) in compY
... | tri< y<p _ _ = {!!}
ins-comm x y z {v} fˣ fʸ (node p lt rt bal) nEq prf | tri≈ _ refl _ with compare x (proj₁ p)
... | tri< x<p _ _ = {!!}
... | tri≈ _ refl _ rewrite compY = ⊥-elim (nEq refl)
... | tri> _ _ p<x with insertWith x fˣ ⦃ [ p<x ]ᴿ ⦄ rt in insX
... | (i , rt') with compare z (proj₁ p)
... | tri< z<p _ _ = {!prf'!}
  where
    prf' = inᴸ-joinᴿ⁺ lt (i , rt') bal [ z<p ]ᴿ prf
... | tri≈ _ refl _ = {!insert∈ (proj₁ p) v ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ (proj₂ (joinʳ⁺ p lt (i , rt') bal))!}
... | tri> _ _ p<z = {!!}
  where
    prf' = inᴿ-joinᴿ⁺ lt (i , rt') bal [ p<z ]ᴿ prf
ins-comm x y z fˣ fʸ (node p lt rt bal) nEq prf | tri> _ _ p<y with compare x (proj₁ p) in compX
... | tri< x<p _ _ = {!!}
... | tri≈ _ refl _ rewrite compY = {!!}
... | tri> _ _ p<x = {!!}

-- -}
-- -}
-- -}
-- -}
