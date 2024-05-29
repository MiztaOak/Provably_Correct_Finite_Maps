{-# OPTIONS --erasure #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet using (OrdSet; toStrictTotalOrder)

module Map.Proofs.Deletion.Proofs {k ℓ₁ v} (order : OrdSet k ℓ₁) (V : Set v) where
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
open import Map.Proofs.Insertion.Helpers order V using (inᴸ-joinᴿ⁺; inᴿ-joinᴸ⁺; inᴸ-joinᴸ⁺)
open import Map.Proofs.Deletion.Helpers order V

---------------------------------------------------------------------------------
-- del-∈
---------------------------------------------------------------------------------
del-∈ : ∀ {l u : Key⁺} {h : ℕ}
        (k : Key) (m : BOBMap V l u h)
        ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
        → k ∉ proj₂ (delete k m)
del-∈ k leaf ()
del-∈ k (node p lm rm b) ∉dM with compare k (proj₁ p)
... | tri< a _ _ = del-∈ k lm ⦃ k<u = [ a ]ᴿ ⦄ prfᴸ
  where
    prfᴸ = ∈ᴸ-joinᴸ⁻ ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ (delete k ⦃ p≤u = [ a ]ᴿ ⦄ lm) rm b [ a ]ᴿ ∉dM
... | tri≈ _ refl _ = notHere {rm = rm} (notInLeft k lm) ∉dM
  where
    notHere : ∀ {l u : Key⁺} {hl hr h : ℕ}
              {k : Key}
              {lm : BOBMap V l [ k ] hl}
              {rm : BOBMap V [ k ] u hr}
              {b : hl ~ hr ⊔ h}
              → ¬ k ∈ lm
              → ¬ (k ∈ proj₂ (join lm rm b))
    notHere {k = k} {lm} {leaf} {~- } ¬lm prf = ¬lm (inRaise' prf)
    notHere {k = k} {lm} {leaf} {~0} ¬lm ()
    notHere {l} {k = k} {lm} rm@{node _ _ _ _} {b} ¬lm prf with uncons rm
    ... | cons head l<u tail with
      ∈ᴸ-joinᴿ⁻ ⦃ trans⁺ l (mklim lm) l<u ⦄ ⦃ mklim (proj₂ tail) ⦄ (raise ⦃ l<u ⦄ lm) tail b l<u prf
    ... | prfᴸ = ¬lm (inRaise' ⦃ l<u ⦄ prfᴸ)
... | tri> _ _ c = del-∈ k rm ⦃ [ c ]ᴿ ⦄ prfᴿ
  where
    prfᴿ = ∈ᴿ-joinᴿ⁻ ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ lm (delete k ⦃ [ c ]ᴿ ⦄ rm) b [ c ]ᴿ ∉dM

---------------------------------------------------------------------------------
-- del-safe
---------------------------------------------------------------------------------
del-safe : ∀ {l u : Key⁺} {h : ℕ} (k k' : Key) {v : V} (m : BOBMap V l u h)
           ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
           → k' ↦ v ∈ m
           → k ≢ k'
           → k' ↦ v ∈ proj₂ (delete k m)
del-safe k k' leaf () nEq
del-safe k k' (node .(k' , _) lm rm b) (here refl) nEq with compare k k'
... | tri< a _ _ = herejoinᴸ⁻ (delete k ⦃ p≤u = [ a ]ᴿ ⦄ lm) rm b
... | tri≈ _ refl _ = ⊥-elim (nEq refl)
... | tri> _ _ c = herejoinᴿ⁻ lm (delete k ⦃ [ c ]ᴿ ⦄ rm) b
del-safe k k' (node p lm rm b) (left ⦃ k'<p ⦄ prf) nEq with compare k (proj₁ p)
... | tri< a _ _ = anyᴸ-joinᴸ⁻ lm⁻ rm b k'<p prfᴸ
  where
    prfᴸ = del-safe k k' lm ⦃ k<u = [ a ]ᴿ ⦄ prf nEq
    lm⁻ = delete k ⦃ p≤u = [ a ]ᴿ ⦄ lm
... | tri≈ _ refl _ = anyJoinᴸ lm rm b prf [ k'<p ]-lower
... | tri> _ _ c = anyᴸ-joinᴿ⁻ lm rm⁻ b k'<p prf
  where
    rm⁻ = delete k ⦃ [ c ]ᴿ ⦄ rm
del-safe k k' (node p lm rm b) (right ⦃ p<k' ⦄ prf) nEq with compare k (proj₁ p)
... | tri< a _ _ = anyᴿ-joinᴸ⁻ lm⁻ rm b p<k' prf
  where
    lm⁻ = delete k ⦃ p≤u = [ a ]ᴿ ⦄ lm
... | tri≈ _ refl _ = anyJoinᴿ lm rm b prf p<k'
... | tri> _ _ c = anyᴿ-joinᴿ⁻ lm rm⁻ b p<k' prfᴿ
  where
    prfᴿ = del-safe k k' rm ⦃ [ c ]ᴿ ⦄ prf nEq
    rm⁻ = delete k ⦃ [ c ]ᴿ ⦄ rm

del-safe' : ∀ {l u : Key⁺} {h : ℕ} (k : Key) {v : V} (m : BOBMap V l u h)
           ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
           → ¬ (k ↦ v ∈ proj₂ (delete k m))
del-safe' k leaf ()
del-safe' k (node p lm rm bal) prf with compare k (proj₁ p)
... | tri< k<p _ _ =
  del-safe' k lm ⦃ k<u = [ k<p ]ᴿ ⦄ (inᴸ-joinᴸ⁻ (delete k ⦃ p≤u = [ k<p ]ᴿ ⦄ lm) rm bal [ k<p ]ᴿ prf)
... | tri> _ _ p<k =
  del-safe' k rm ⦃ [ p<k ]ᴿ ⦄ (inᴿ-joinᴿ⁻ lm (delete k ⦃ [ p<k ]ᴿ ⦄ rm) bal [ p<k ]ᴿ prf)
... | tri≈ _ refl _ = notInJoin k lm rm bal prf

---------------------------------------------------------------------------------
-- del-∉
---------------------------------------------------------------------------------
del-∉del⊆ : ∀ {l u : Key⁺} {h : ℕ} (k : Key)
        ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
        (m : BOBMap V l u h)
        → k ∉ m
        → proj₂ (delete k m) ⊆ m
del-∉del⊆ k leaf prf k' v ()
del-∉del⊆ k (node p lm rm bal) prf k' v prf' with compare k (proj₁ p)
... | tri≈ _ refl _ = ⊥-elim (prf (here tt))
del-∉del⊆ k (node p lm rm bal) prf k' v prf' | tri< k<p _ _ with compare k' (proj₁ p)
... | tri< k'<p _ _ = left ⦃ [ k'<p ]ᴿ ⦄ (del-∉del⊆ k ⦃ k<u = [ k<p ]ᴿ ⦄ lm (∉Left k<p prf) k' v prfᴸ)
  where
    lm⁻ = delete k ⦃ p≤u = [ k<p ]ᴿ ⦄ lm
    prfᴸ = inᴸ-joinᴸ⁻ lm⁻ rm bal [ k'<p ]ᴿ prf'
... | tri≈ _ refl _ = here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ prfC
  where
    lm⁻ = delete k ⦃ p≤u = [ k<p ]ᴿ ⦄ lm
    prfC = inC-joinᴸ⁻ lm⁻ rm bal prf'
... | tri> _ _ p<k' = right ⦃ [ p<k' ]ᴿ ⦄ prfᴿ
  where
    lm⁻ = delete k ⦃ p≤u = [ k<p ]ᴿ ⦄ lm
    prfᴿ = inᴿ-joinᴸ⁻ lm⁻ rm bal [ p<k' ]ᴿ prf'
del-∉del⊆ k (node p lm rm bal) prf k' v prf' | tri> _ _ p<k with compare k' (proj₁ p)
... | tri< k'<p _ _ = left ⦃ [ k'<p ]ᴿ ⦄ prfᴸ
  where
    rm⁻ = delete k ⦃ [ p<k ]ᴿ ⦄ rm
    prfᴸ = inᴸ-joinᴿ⁻ lm rm⁻ bal [ k'<p ]ᴿ prf'
... | tri≈ _ refl _ = here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ prfC
  where
    rm⁻ = delete k ⦃ [ p<k ]ᴿ ⦄ rm
    prfC = inC-joinᴿ⁻ lm rm⁻ bal prf'
... | tri> _ _ p<k' = right ⦃ [ p<k' ]ᴿ ⦄ (del-∉del⊆ k ⦃ [ p<k ]ᴿ ⦄ rm (∉Right p<k prf) k' v prfᴿ)
  where
    rm⁻ = delete k ⦃ [ p<k ]ᴿ ⦄ rm
    prfᴿ = inᴿ-joinᴿ⁻ lm rm⁻ bal [ p<k' ]ᴿ prf'


del-∉m⊆ : ∀ {l u : Key⁺} {h : ℕ} (k : Key)
        ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
        (m : BOBMap V l u h)
        → k ∉ m
        → m ⊆ proj₂ (delete k m)
del-∉m⊆ k m prf k' v prf' = del-safe k k' m prf' (∈Contradiction prf (↦∈To∈ prf'))

del-∉ : ∀ {l u : Key⁺} {h : ℕ} (k : Key)
        ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
        (m : BOBMap V l u h)
        → k ∉ m
        → proj₂ (delete k m) ≐ m
del-∉ k m prf = (del-∉del⊆ k m prf) , (del-∉m⊆ k m prf)

---------------------------------------------------------------------------------
-- proof that delete does not add any elements to the map
---------------------------------------------------------------------------------
del-noAdd : ∀ {l u : Key⁺} {h : ℕ} (k k' : Key) {v : V}
  ⦃ @erased l<k : l <⁺ [ k' ] ⦄ ⦃ @erased k<u : [ k' ] <⁺ u ⦄
  → (m : BOBMap V l u h)
  → k ↦ v ∈ proj₂ (delete k' m)
  → k ↦ v ∈ m
del-noAdd k k' leaf ()
del-noAdd k k' (node p lm rm bal) prf with compare k k'
del-noAdd k k' (node p lm rm bal) prf | tri< k<k' _ _ with compare k' (proj₁ p)
... | tri< k'<p _ _ = left ⦃ [ k<p ]ᴿ ⦄ (del-noAdd k k' ⦃ k<u = [ k'<p ]ᴿ ⦄ lm prf')
  where
    k<p = trans k<k' k'<p
    prf' = inᴸ-joinᴸ⁻ (delete k' ⦃ p≤u = [ k'<p ]ᴿ ⦄ lm) rm bal [ k<p ]ᴿ prf
... | tri≈ _ refl _ with compare k (proj₁ p)
... | tri< k<p _ _ = left ⦃ [ k<p ]ᴿ ⦄ (inJoinᴸ lm rm bal prf k<p)
... | tri≈ _ refl _ = ⊥-elim (notInJoin k lm rm bal prf)
... | tri> _ _ p<k = right ⦃ [ p<k ]ᴿ ⦄ (inJoinᴿ lm rm bal prf p<k)
del-noAdd k k' (node p lm rm bal) prf | tri< k<k' _ _ | tri> _ _ p<k' with compare k (proj₁ p)
... | tri< k<p _ _  = left ⦃ [ k<p ]ᴿ ⦄ prf'
  where
    prf' = inᴸ-joinᴿ⁻ lm (delete k' ⦃ [ p<k' ]ᴿ ⦄ rm) bal [ k<p ]ᴿ prf
... | tri≈ _ refl _ rewrite inC-joinᴿ⁻ lm (delete k' ⦃ [ p<k' ]ᴿ ⦄ rm) bal prf =
  here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ refl
... | tri> _ _ p<k = right ⦃ [ p<k ]ᴿ ⦄ (del-noAdd k k' ⦃ [ p<k' ]ᴿ ⦄ rm prf')
  where
    prf' = inᴿ-joinᴿ⁻ lm (delete k' ⦃ [ p<k' ]ᴿ ⦄ rm) bal [ p<k ]ᴿ prf
del-noAdd k k' (node p lm rm bal) prf | tri≈ _ refl _ = ⊥-elim (del-safe' k' (node p lm rm bal) prf)
del-noAdd k k' (node p lm rm bal) prf | tri> _ _ k'<k with compare k' (proj₁ p)
... | tri> _ _ p<k' = right ⦃ [ p<k ]ᴿ ⦄ (del-noAdd k k' ⦃ [ p<k' ]ᴿ ⦄ rm prf')
  where
    p<k = trans p<k' k'<k
    prf' = inᴿ-joinᴿ⁻ lm (delete k' ⦃ [ p<k' ]ᴿ ⦄ rm) bal [ p<k ]ᴿ prf
... | tri< k'<p _ _ with compare k (proj₁ p)
... | tri< k<p _ _ = left ⦃ [ k<p ]ᴿ ⦄ (del-noAdd k k' ⦃ k<u = [ k'<p ]ᴿ ⦄ lm prf')
  where
    prf' = inᴸ-joinᴸ⁻ (delete k' ⦃ p≤u = [ k'<p ]ᴿ ⦄ lm) rm bal [ k<p ]ᴿ prf
... | tri≈ _ refl _ rewrite inC-joinᴸ⁻ (delete k' ⦃ p≤u = [ k'<p ]ᴿ ⦄ lm) rm bal prf =
  here ⦃ mklim lm ⦄ ⦃ mklim rm ⦄ refl
... | tri> _ _ p<k = right ⦃ [ p<k ]ᴿ ⦄ prf'
  where
    prf' = inᴿ-joinᴸ⁻ (delete k' ⦃ p≤u = [ k'<p ]ᴿ ⦄ lm) rm bal [ p<k ]ᴿ prf
del-noAdd k k' (node p lm rm bal) prf | tri> _ _ k'<k | tri≈ _ refl _ with compare k (proj₁ p)
... | tri< k<p _ _ = left ⦃ [ k<p ]ᴿ ⦄ (inJoinᴸ lm rm bal prf k<p)
... | tri≈ _ refl _ = ⊥-elim (notInJoin (proj₁ p) lm rm bal prf)
... | tri> _ _ p<k = right ⦃ [ p<k ]ᴿ ⦄ (inJoinᴿ lm rm bal prf p<k)

---------------------------------------------------------------------------------
-- delete commutativity
---------------------------------------------------------------------------------
delete-joinR→R : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (x y z : Key)
    (p : Key × V)
    {v : V}
    ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ p<x : [ proj₁ p ] <⁺ [ x ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
    ⦃ l<y : l <⁺ [ y ] ⦄ ⦃ p<y : [ proj₁ p ] <⁺ [ y ] ⦄ ⦃ y<u : [ y ] <⁺ u ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → z ↦ v ∈ (proj₂ (delete x (proj₂ (joinʳ⁻ p lt (delete y rt) bal))))
    → z ↦ v ∈ (proj₂ (delete y (proj₂ (joinʳ⁻ p lt (delete x rt) bal))))
delete-joinR→R x y z p ⦃ p<y = p<y ⦄ lt rt bal prf with delete y rt in delEq
... | rtʸ with joinʳ⁻ p lt rtʸ bal in eqJoin
... | rt⁺ with del-noAdd z x (proj₂ rt⁺) prf
... | prf' rewrite sym eqJoin with isEq? y z
... | inj₁ refl rewrite sym delEq = ⊥-elim (del-safe' z rt delPrf)
  where
    delPrf = inᴿ-joinᴿ⁻ lt (delete z rt) bal p<y prf'
... | inj₂ nEqY with compare z (proj₁ p)
... | tri< z<p _ _ = del-safe y z (proj₂ (joinʳ⁻ p lt (delete x rt) bal)) prfJoin nEqY
  where
    prfL = inᴸ-joinᴿ⁻ lt rtʸ bal [ z<p ]ᴿ prf'
    prfJoin = anyᴸ-joinᴿ⁻ lt (delete x rt) bal [ z<p ]ᴿ prfL
... | tri≈ _ refl _ rewrite inC-joinᴿ⁻ lt rtʸ bal prf' =
  del-safe y z (proj₂ (joinʳ⁻ p lt (delete x rt) bal)) prfJoin nEqY
  where
    prfJoin = herejoinᴿ⁻ lt (delete x rt) bal
... | tri> _ _ p<z with isEq? x z
... | inj₁ refl = ⊥-elim (del-safe' x (proj₂ (joinʳ⁻ p lt rtʸ bal)) prf)
... | inj₂ nEqX rewrite sym delEq = del-safe y z m prfJoin nEqY
  where
    m = proj₂ (joinʳ⁻ p lt (delete x rt) bal)
    prfᴿ = inᴿ-joinᴿ⁻ lt (delete y rt) bal [ p<z ]ᴿ prf'
    prfDel = del-noAdd z y rt prfᴿ
    delX = del-safe x z rt prfDel nEqX
    prfJoin = anyᴿ-joinᴿ⁻ lt (delete x rt) bal [ p<z ]ᴿ delX

delete-joinL→L : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (x y z : Key)
    (p : Key × V)
    {v : V}
    ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ x<p : [ x ] <⁺ [ proj₁ p ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
    ⦃ l<y : l <⁺ [ y ] ⦄ ⦃ y<p : [ y ] <⁺ [ proj₁ p ] ⦄ ⦃ y<u : [ y ] <⁺ u ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → z ↦ v ∈ (proj₂ (delete x (proj₂ (joinˡ⁻ p (delete y lt) rt bal))))
    → z ↦ v ∈ (proj₂ (delete y (proj₂ (joinˡ⁻ p (delete x lt) rt bal))))
delete-joinL→L x y z p ⦃ y<p = y<p ⦄ lt rt bal prf with delete y lt in delEq
... | ltʸ with joinˡ⁻ p ltʸ rt bal in eqJoin
... | lt⁺ with del-noAdd z x (proj₂ lt⁺) prf
... | prf' rewrite sym eqJoin with isEq? y z
... | inj₁ refl rewrite sym delEq = ⊥-elim (del-safe' z lt delPrf)
  where
    delPrf = inᴸ-joinᴸ⁻ (delete z lt) rt bal y<p prf'
... | inj₂ y≢z with compare z (proj₁ p)
... | tri> _ _ p<z = del-safe y z (proj₂ (joinˡ⁻ p (delete x lt) rt bal)) prfJoin y≢z
  where
    prfR = inᴿ-joinᴸ⁻ ltʸ rt bal [ p<z ]ᴿ prf'
    prfJoin = anyᴿ-joinᴸ⁻ (delete x lt) rt bal [ p<z ]ᴿ prfR
... | tri≈ _ refl _ rewrite inC-joinᴸ⁻ ltʸ rt bal prf' = del-safe y z m prfJoin y≢z
  where
    m = proj₂ (joinˡ⁻ p (delete x lt) rt bal)
    prfJoin = herejoinᴸ⁻ (delete x lt) rt bal
... | tri< z<p _ _ with isEq? x z
... | inj₁ refl = ⊥-elim (del-safe' x (proj₂ (joinˡ⁻ p ltʸ rt bal)) prf)
... | inj₂ x≢z rewrite sym delEq = del-safe y z m prfJoin y≢z
  where
    m = proj₂ (joinˡ⁻ p (delete x lt) rt bal)
    prfᴸ = inᴸ-joinᴸ⁻ (delete y lt) rt bal [ z<p ]ᴿ prf'
    prfDel = del-noAdd z y lt prfᴸ
    delX = del-safe x z lt prfDel x≢z
    prfJoin = anyᴸ-joinᴸ⁻ (delete x lt) rt bal [ z<p ]ᴿ delX

delete-joinL→R : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (x y z : Key)
    (p : Key × V)
    {v : V}
    ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ p<x : [ proj₁ p ] <⁺ [ x ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
    ⦃ l<y : l <⁺ [ y ] ⦄ ⦃ y<p : [ y ] <⁺ [ proj₁ p ] ⦄ ⦃ y<u : [ y ] <⁺ u ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → z ↦ v ∈ (proj₂ (delete x (proj₂ (joinˡ⁻ p (delete y lt) rt bal))))
    → z ↦ v ∈ (proj₂ (delete y (proj₂ (joinʳ⁻ p lt (delete x rt) bal))))
delete-joinL→R x y z p ⦃ y<p = y<p ⦄ lt rt bal prf with delete y lt in delEq
... | ltʸ with joinˡ⁻ p ltʸ rt bal in eqJoin
... | lt⁺ with del-noAdd z x (proj₂ lt⁺) prf
... | prf' rewrite sym eqJoin with isEq? y z
... | inj₁ refl rewrite sym delEq = ⊥-elim (del-safe' z lt delPrf)
  where
    delPrf = inᴸ-joinᴸ⁻ (delete y lt) rt bal y<p prf'
... | inj₂ y≢z rewrite sym delEq with compare z (proj₁ p)
... | tri< z<p _ _ = del-safe y z m prfJoin y≢z
  where
    m = proj₂ (joinʳ⁻ p lt (delete x rt) bal)
    prfDel = inᴸ-joinᴸ⁻ (delete y lt) rt bal [ z<p ]ᴿ prf'
    prfᴸ = del-noAdd z y lt prfDel
    prfJoin = anyᴸ-joinᴿ⁻ lt (delete x rt) bal [ z<p ]ᴿ prfᴸ
... | tri≈ _ refl _ rewrite inC-joinᴸ⁻ (delete y lt) rt bal prf' = del-safe y z m prfJoin y≢z
  where
    m = proj₂ (joinʳ⁻ p lt (delete x rt) bal)
    prfJoin = herejoinᴿ⁻ lt (delete x rt) bal
... | tri> _ _ p<z with isEq? x z
... | inj₁ refl = ⊥-elim (del-safe' z m prf)
  where
    m = proj₂ (joinˡ⁻ p (delete y lt) rt bal)
... | inj₂ x≢z = del-safe y z m prfJoin y≢z
  where
    m = proj₂ (joinʳ⁻ p lt (delete x rt) bal)
    prfᴿ = inᴿ-joinᴸ⁻ (delete y lt) rt bal [ p<z ]ᴿ prf'
    prfDel = del-safe x z rt prfᴿ x≢z
    prfJoin = anyᴿ-joinᴿ⁻ lt (delete x rt) bal [ p<z ]ᴿ prfDel

delete-joinR→L : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (x y z : Key)
    (p : Key × V)
    {v : V}
    ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ x<p : [ x ] <⁺ [ proj₁ p ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
    ⦃ l<y : l <⁺ [ y ] ⦄ ⦃ p<y : [ proj₁ p ] <⁺ [ y ] ⦄ ⦃ y<u : [ y ] <⁺ u ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → z ↦ v ∈ (proj₂ (delete x (proj₂ (joinʳ⁻ p lt (delete y rt) bal))))
    → z ↦ v ∈ (proj₂ (delete y (proj₂ (joinˡ⁻ p (delete x lt) rt bal))))
delete-joinR→L x y z p ⦃ p<y = p<y ⦄ lt rt bal prf with joinʳ⁻ p lt (delete y rt) bal in eqJoin
... | rt⁺ with del-noAdd z x (proj₂ rt⁺) prf
... | prf' with isEq? y z
... | inj₁ refl rewrite sym eqJoin = ⊥-elim (del-safe' z rt delPrf)
  where
    delPrf = inᴿ-joinᴿ⁻ lt (delete y rt) bal p<y prf'
... | inj₂ y≢z rewrite sym eqJoin with compare z (proj₁ p)
... | tri≈ _ refl _ rewrite inC-joinᴿ⁻ lt (delete y rt) bal prf' = del-safe y z m prfJoin y≢z
  where
    m = proj₂ (joinˡ⁻ p (delete x lt) rt bal)
    prfJoin = herejoinᴸ⁻ (delete x lt) rt bal
... | tri> _ _ p<z = del-safe y z m prfJoin y≢z
  where
    m = proj₂ (joinˡ⁻ p (delete x lt) rt bal)
    prfDel = inᴿ-joinᴿ⁻ lt (delete y rt) bal [ p<z ]ᴿ prf'
    prfᴿ = del-noAdd z y rt prfDel
    prfJoin = anyᴿ-joinᴸ⁻ (delete x lt) rt bal [ p<z ]ᴿ prfᴿ
... | tri< z<p _ _ with isEq? x z
... | inj₁ refl = ⊥-elim (del-safe' z m prf)
  where
    m = proj₂ (joinʳ⁻ p lt (delete y rt) bal)
... | inj₂ x≢z = del-safe y z m prfJoin y≢z
  where
    m = proj₂ (joinˡ⁻ p (delete x lt) rt bal)
    prfᴸ = inᴸ-joinᴿ⁻ lt (delete y rt) bal [ z<p ]ᴿ prf'
    prfDel = del-safe x z lt prfᴸ x≢z
    prfJoin = anyᴸ-joinᴸ⁻ (delete x lt) rt bal [ z<p ]ᴿ prfDel

delete-joinL : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (x z : Key)
    (p : Key × V)
    {v : V}
    ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ x<p : [ x ] <⁺ [ proj₁ p ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
    ⦃ l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ p<u : [ proj₁ p ] <⁺ u ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → z ↦ v ∈ (proj₂ (delete (proj₁ p) (proj₂ (joinˡ⁻ p (delete x lt) rt bal))))
    → z ↦ v ∈ (proj₂ (delete x (proj₂ (join lt rt bal))))
delete-joinL x z p lt rt bal prf with joinˡ⁻ p (delete x lt) rt bal in eqJoin
... | lt⁺ with del-noAdd z (proj₁ p) (proj₂ lt⁺) prf
... | prf' rewrite sym eqJoin with compare z (proj₁ p)
delete-joinL x z p lt rt bal prf | lt⁺ | prf' | tri< z<p _ _ with isEq? x z
... | inj₁ refl = ⊥-elim (del-safe' z lt prfDel)
  where
    prfDel = inᴸ-joinᴸ⁻ (delete x lt) rt bal [ z<p ]ᴿ prf'
... | inj₂ x≢z = del-safe x z (proj₂ (join lt rt bal)) prfJoin x≢z
  where
    prfDel = inᴸ-joinᴸ⁻ (delete x lt) rt bal [ z<p ]ᴿ prf'
    prfᴸ = del-noAdd z x lt prfDel
    prfJoin = anyJoinᴸ lt rt bal prfᴸ z<p
delete-joinL x z p lt rt bal prf | lt⁺ | prf' | tri≈ _ refl _ = ⊥-elim (del-safe' z m prf)
  where
    m = proj₂ (joinˡ⁻ p (delete x lt) rt bal)
delete-joinL x z p ⦃ x<p = x<p ⦄ lt rt bal prf | lt⁺ | prf' | tri> ¬z<p _ p<z with isEq? x z
... | inj₁ refl = ⊥-elim (¬z<p [ x<p ]-lower)
... | inj₂ x≢z = del-safe x z (proj₂ (join lt rt bal)) prfJoin x≢z
  where
    prfᴿ = inᴿ-joinᴸ⁻ (delete x lt) rt bal [ p<z ]ᴿ prf'
    prfJoin = anyJoinᴿ lt rt bal prfᴿ [ p<z ]ᴿ

delete-joinR : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (x z : Key)
    (p : Key × V)
    {v : V}
    ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ p<x : [ proj₁ p ] <⁺ [ x ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
    ⦃ l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ p<u : [ proj₁ p ] <⁺ u ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → z ↦ v ∈ (proj₂ (delete (proj₁ p) (proj₂ (joinʳ⁻ p lt (delete x rt) bal))))
    → z ↦ v ∈ (proj₂ (delete x (proj₂ (join lt rt bal))))
delete-joinR x z p lt rt bal prf with joinʳ⁻ p lt (delete x rt) bal in eqJoin
... | rt⁺ with del-noAdd z (proj₁ p) (proj₂ rt⁺) prf
... | prf' rewrite sym eqJoin with compare z (proj₁ p)
delete-joinR x z p ⦃ p<x = p<x ⦄ lt rt bal prf | rt⁺ | prf' | tri< z<p _ ¬p<z with isEq? x z
... | inj₁ refl = ⊥-elim (¬p<z [ p<x ]-lower)
... | inj₂ x≢z = del-safe x z (proj₂ (join lt rt bal)) prfJoin x≢z
  where
    prfᴸ = inᴸ-joinᴿ⁻ lt (delete x rt) bal [ z<p ]ᴿ prf'
    prfJoin = anyJoinᴸ lt rt bal prfᴸ z<p
delete-joinR x z p lt rt bal prf | rt⁺ | prf' | tri≈ _ refl _ = ⊥-elim (del-safe' z m prf)
  where
    m = proj₂ (joinʳ⁻ p lt (delete x rt) bal)
delete-joinR x z p lt rt bal prf | rt⁺ | prf' | tri> _ _ p<z with isEq? x z
... | inj₁ refl = ⊥-elim (del-safe' z rt prfDel)
  where
    prfDel = inᴿ-joinᴿ⁻ lt (delete x rt) bal [ p<z ]ᴿ prf'
... | inj₂ x≢z = del-safe x z (proj₂ (join lt rt bal)) prfJoin x≢z
  where
    prfDel = inᴿ-joinᴿ⁻ lt (delete x rt) bal [ p<z ]ᴿ prf'
    prfᴿ = del-noAdd z x rt prfDel
    prfJoin = anyJoinᴿ lt rt bal prfᴿ [ p<z ]ᴿ

delete-join→L : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (x z : Key)
    (p : Key × V)
    {v : V}
    ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ x<p : [ x ] <⁺ [ proj₁ p ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
    ⦃ l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ p<u : [ proj₁ p ] <⁺ u ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → z ↦ v ∈ (proj₂ (delete x (proj₂ (join lt rt bal))))
    → z ↦ v ∈ (proj₂ (delete (proj₁ p) (proj₂ (joinˡ⁻ p (delete x lt) rt bal))))
delete-join→L x z p lt rt bal prf with isEq? x z
... | inj₁ refl = ⊥-elim (del-safe' x (proj₂ (join lt rt bal)) prf)
... | inj₂ x≢z with del-noAdd z x (proj₂ (join lt rt bal)) prf
... | prfJoin with compare z (proj₁ p)
... | tri< z<p z≢p _ = del-safe (proj₁ p) z m prfJoinᴸ λ x → z≢p (sym x)
  where
    m = proj₂ (joinˡ⁻ p (delete x lt) rt bal)
    prfᴸ = inJoinᴸ lt rt bal prfJoin z<p
    prfDel = del-safe x z lt prfᴸ x≢z
    prfJoinᴸ = anyᴸ-joinᴸ⁻ (delete x lt) rt bal [ z<p ]ᴿ prfDel
... | tri≈ _ refl _ = ⊥-elim (notInJoin z lt rt bal prfJoin)
... | tri> _ p≢z p<z = del-safe (proj₁ p) z m prfJoinᴸ λ x → p≢z (sym x)
  where
    m = proj₂ (joinˡ⁻ p (delete x lt) rt bal)
    prfᴿ = inJoinᴿ lt rt bal prfJoin p<z
    prfJoinᴸ = anyᴿ-joinᴸ⁻ (delete x lt) rt bal [ p<z ]ᴿ prfᴿ

delete-join→R : ∀ {l u : Key⁺} {hl hr h : ℕ}
    (x z : Key)
    (p : Key × V)
    {v : V}
    ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ p<x : [ proj₁ p ] <⁺ [ x ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
    ⦃ l<p : l <⁺ [ proj₁ p ] ⦄ ⦃ p<u : [ proj₁ p ] <⁺ u ⦄
    (lt : BOBMap V l [ proj₁ p ] hl)
    (rt : BOBMap V [ proj₁ p ] u hr)
    (bal : hl ~ hr ⊔ h)
    → z ↦ v ∈ (proj₂ (delete x (proj₂ (join lt rt bal))))
    → z ↦ v ∈ (proj₂ (delete (proj₁ p) (proj₂ (joinʳ⁻ p lt (delete x rt) bal))))
delete-join→R x z p lt rt bal prf with isEq? x z
... | inj₁ refl = ⊥-elim (del-safe' x (proj₂ (join lt rt bal)) prf)
... | inj₂ x≢z with del-noAdd z x (proj₂ (join lt rt bal)) prf
... | prfJoin with compare z (proj₁ p)
... | tri< z<p z≢p _ = del-safe (proj₁ p) z m prfJoinᴿ λ x → z≢p (sym x)
  where
    m = proj₂ (joinʳ⁻ p lt (delete x rt) bal)
    prfᴸ = inJoinᴸ lt rt bal prfJoin z<p
    prfJoinᴿ = anyᴸ-joinᴿ⁻ lt (delete x rt) bal [ z<p ]ᴿ prfᴸ
... | tri≈ _ refl _ = ⊥-elim (notInJoin z lt rt bal prfJoin)
... | tri> _ z≢p p<z = del-safe (proj₁ p) z m prfJoinᴿ λ x → z≢p (sym x)
  where
    m = proj₂ (joinʳ⁻ p lt (delete x rt) bal)
    prfᴿ = inJoinᴿ lt rt bal prfJoin p<z
    prfDel = del-safe x z rt prfᴿ x≢z
    prfJoinᴿ = anyᴿ-joinᴿ⁻ lt (delete x rt) bal [ p<z ]ᴿ prfDel

del-comm : ∀ {l u : Key⁺} {h : ℕ}
  → (x y k : Key)
  → {v : V}
  ⦃ l<x : l <⁺ [ x ] ⦄ ⦃ x<u : [ x ] <⁺ u ⦄
  ⦃ l<y : l <⁺ [ y ] ⦄ ⦃ y<u : [ y ] <⁺ u ⦄
  → (m : BOBMap V l u h)
  → k ↦ v ∈ proj₂ (delete x (proj₂ (delete y m)))
  → k ↦ v ∈ proj₂ (delete y (proj₂ (delete x m)))
del-comm x y k (node p lm rm bal) prf with isEq? x y
... | inj₁ refl = prf
... | inj₂ x≢y with compare y (proj₁ p)
del-comm x y k (node p lm rm bal) prf | inj₂ x≢y | tri< y<p _ _ with compare x (proj₁ p)
... | tri< x<p _ _ = delete-joinL→L x y k p ⦃ x<p = [ x<p ]ᴿ ⦄ ⦃ y<p = [ y<p ]ᴿ ⦄ lm rm bal prf
... | tri≈ _ refl _ = delete-joinL y k p ⦃ x<p = [ y<p ]ᴿ ⦄ lm rm bal prf
... | tri> _ _ p<x = delete-joinL→R x y k p ⦃ p<x = [ p<x ]ᴿ ⦄ ⦃ y<p = [ y<p ]ᴿ ⦄ lm rm bal prf
del-comm x y k (node p lm rm bal) prf | inj₂ x≢y | tri≈ _ refl _ with compare x (proj₁ p)
... | tri< x<p _ _ = delete-join→L x k p ⦃ x<p = [ x<p ]ᴿ ⦄ lm rm bal prf
... | tri≈ _ refl _ = prf
... | tri> _ _ p<x = delete-join→R x k p ⦃ p<x = [ p<x ]ᴿ ⦄ lm rm bal prf
del-comm x y k (node p lm rm bal) prf | inj₂ x≢y | tri> _ _ p<y with compare x (proj₁ p)
... | tri< x<p _ _ = delete-joinR→L x y k p ⦃ x<p = [ x<p ]ᴿ ⦄ ⦃ p<y = [ p<y ]ᴿ ⦄ lm rm bal prf
... | tri≈ _ refl _ = delete-joinR y k p ⦃ p<x = [ p<y ]ᴿ ⦄ lm rm bal prf
... | tri> _ _ p<x = delete-joinR→R x y k p ⦃ p<x = [ p<x ]ᴿ ⦄ ⦃ p<y = [ p<y ]ᴿ ⦄ lm rm bal prf

-- -}
-- -}
-- -}
-- -}
-- -}
