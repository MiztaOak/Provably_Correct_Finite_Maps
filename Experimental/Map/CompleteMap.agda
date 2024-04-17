module Map.CompleteMap where

open import Level renaming (suc to lsuc; zero to lzero)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Sum

private
  variable
    ℓ ℓ' : Level

module _ {ℓ₁ : Level} {K : Set ℓ} {V : Set ℓ'} where

  open import Map.BasicMap using (BMap)
  open import Map.DeletableMap using (DMap)
  open import Map.MergableMap using (MMap)

  record CMap (Map : Set (ℓ ⊔ ℓ' ⊔ ℓ₁)) : Set (lsuc (ℓ ⊔ ℓ' ⊔ ℓ₁)) where
    constructor mkCMap

    field
      dMap    : DMap {ℓ} {ℓ'} {ℓ₁} {K} {V} Map
      mMap    : MMap {ℓ} {ℓ'} {ℓ₁} {K} {V} Map

    private
      module DeleteMap = Map.DeletableMap.DMap dMap
      module MergeMap = Map.MergableMap.MMap mMap

    open MergeMap public
    open DeleteMap public using (delete; del-∉; del-∈; del-safe)
