module Map.CorrectAll where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Unary using (Pred)
open import Data.Product

private
  variable
    ℓ ℓ' : Level

module _ {ℓ₁ ℓₐ : Level} {K : Set ℓ} {V : Set ℓ'} where

  open import Map.BasicMap using (BMap)

  record CorrectAll (Map : Set (ℓ ⊔ ℓ' ⊔ ℓ₁)) (bMap : BMap {ℓ} {ℓ'} {ℓ₁} {K} {V} Map) :
    Set (lsuc (ℓ ⊔ ℓ' ⊔ ℓ₁ ⊔ ℓₐ)) where
    field
   --   bMap : BMap {ℓ} {ℓ'} {ℓ₁} {K} {V} Map
      All : Pred (K × V) ℓₐ → Map → Set (ℓ ⊔ ℓ' ⊔ ℓ₁ ⊔ ℓₐ)

    private
      module BasicMap = Map.BasicMap.BMap bMap

    open BasicMap

    field
      allInsert : {P : Pred (K × V) ℓₐ} {k : K} {v : V} {m : Map}
        → P (k , v) → All P m → All P (insert k v m)

      allLookup : {P : Pred (K × V) ℓₐ} {k : K} {v : V} {m : Map}
        → k ↦ v ∈ m → All P m → P (k , v)
