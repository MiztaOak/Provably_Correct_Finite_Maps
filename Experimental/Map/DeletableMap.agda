module Map.DeletableMap where

open import Level renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality

private
  variable
    ℓ ℓ' : Level

module _ {ℓ₁ : Level} {K : Set ℓ} {V : Set ℓ'} where

  open import Map.BasicMap using (BMap)

  record DMap (Map : Set (ℓ ⊔ ℓ' ⊔ ℓ₁)) : Set (lsuc (ℓ ⊔ ℓ' ⊔ ℓ₁)) where
    constructor mkDMap

    field
      bMap    : BMap {ℓ} {ℓ'} {ℓ₁} {K} {V} Map
      delete  : K → Map → Map

    private
      module BaseMap = Map.BasicMap.BMap bMap

    open BaseMap public

    field
      ---------------------------------------------------------------------------------
      -- Deletion properties
      ---------------------------------------------------------------------------------
      del-∉ : ∀ {k m} → k ∉ m → delete k m ≐ m
      del-∈ : ∀ {k m} → k ∈ m → k ∉ delete k m
      del-safe : ∀ {k k' v m} → k' ↦ v ∈ m → k ≢ k' → k' ↦ v ∈ delete k m
      del-comm : ∀ k k' m → delete k (delete k' m) ≐ delete k' (delete k m)
