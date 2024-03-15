{-# OPTIONS --erasure #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet using (OrdSet; toStrictTotalOrder)

module Map.Proofs.DeletionProofs {k ℓ₁ v} (order : OrdSet k ℓ₁) (V : Set v) where
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
-- del-∉
---------------------------------------------------------------------------------
del-∉ : ∀ {l u : Key⁺} {h : ℕ} (k : Key)
        ⦃ @erased l<k : l <⁺ [ k ] ⦄ ⦃ @erased k<u : [ k ] <⁺ u ⦄
        (m : BOBMap V l u h)
        → k ∉ m
        → proj₂ (delete k m) ≐ m
del-∉ k leaf prf = (λ _ _ x → x) , λ _ _ x → x -- should this be allowed?
del-∉ k (node p lm rm bal) prf with compare k (proj₁ p)
... | tri< a ¬b ¬c = {!!}
... | tri≈ ¬a refl ¬c = ⊥-elim (prf (here tt))
... | tri> ¬a ¬b c = (λ k' v x → {!!}) , λ k' v x → {!!}
