module Map.MergableMap where

open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Sum
open import Data.Product

private
  variable
    ℓ ℓ' : Level

module _ {ℓ₁ : Level} {K : Set ℓ} {V : Set ℓ'} where

  open import Map.BasicMap using (BMap)

  record MMap (Map : Set (ℓ ⊔ ℓ' ⊔ ℓ₁)) : Set (lsuc (ℓ ⊔ ℓ' ⊔ ℓ₁)) where
    constructor mkMMap

    field
      bMap    : BMap {ℓ} {ℓ'} {ℓ₁} {K} {V} Map
      unionWith : (V → Maybe V → V) → Map → Map → Map

    private
      module BaseMap = Map.BasicMap.BMap bMap

    open BaseMap public

    field
     ---------------------------------------------------------------------------------
      -- Union Properties
      ---------------------------------------------------------------------------------
      ∪-∅ᴸ : ∀ m f → unionWith f m ∅ ≐ m
      ∪-∅ᴿ : ∀ m f → unionWith f ∅ m ≐ m
      ∪-∅ : ∀ m f → unionWith f m ∅ ≐ unionWith f ∅ m

      ∪-∈ : ∀ m1 m2 f k
            → k ∈ unionWith f m1 m2
            → k ∈ m1 ⊎ k ∈ m2 ⊎ (k ∈ m1 × k ∈ m2)

      -- safety prop of above?
      ∪-∈' : ∀ m1 m2 f k
            → k ∈ m1 ⊎ k ∈ m2
            → k ∈ unionWith f m1 m2

      -- TODO I think this might be right biased (recall we split m₁)
      ∪-safe : ∀ k v₁ v₂ m₁ m₂ f
        → k ↦ v₁ ∈ m₁
        → k ↦ v₂ ∈ m₂
        → k ↦ f v₁ (just v₂) ∈ unionWith f m₂ m₁

      ∪-safe-left : ∀ k v m₁ m₂ f
        → k ↦ v ∈ m₁
        → k ∉ m₂
        → k ↦ f v nothing ∈ unionWith f m₁ m₂

      ∪-safe-right : ∀ k v m₁ m₂ f
        → k ∉ m₁
        → k ↦ v ∈ m₂
        → k ↦ v ∈ unionWith f m₁ m₂

      -- do we need to show source of this? comes from formal-prelude
      ∪-cong : ∀ f m₁ m₂ m₃
        → m₁ ≐ m₂
        → unionWith f m₁ m₃ ≐ unionWith f m₂ m₃
