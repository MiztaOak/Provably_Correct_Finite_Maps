module Map.MergableMap where

open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Sum

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
            → k ∈ m1 ⊎ k ∈ m2

      -- safety prop of above?
      ∪-∈' : ∀ m1 m2 f k
            → k ∈ m1 ⊎ k ∈ m2
            → k ∈ unionWith f m1 m2
