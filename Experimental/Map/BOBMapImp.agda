module Map.BOBMapImp where

open import Prelude hiding (_×_; _,_) renaming (⊥ to ⊥'; ⊤ to ⊤')
open import OrdSet
open import Level using (Level; _⊔_)
open import Map.BasicMap
import Map.BOBMap
open import Data.Nat.Base using (ℕ)
open import Data.Product hiding (map)
open import Function.Base
open import Relation.Unary using (Pred)
open import Data.Empty using (⊥)

private
  variable
    ℓ ℓ' ℓₚ : Level

data Map {K : Set ℓ} (V : Set ℓ') (R : OSet K) : Set (ℓ ⊔ ℓ') where
  map : ∀ {h} → Map.BOBMap.Map.BOBMap V R (⊥' , ⊤') h → Map V R

data AnyM {K : Set ℓ} {V : Set ℓ'} {R : OSet K} (P : Pred (K × V) ℓₚ) :
  Map V R → Set (ℓ ⊔ ℓ' ⊔ ℓₚ) where
    map : ∀ {h t} → Map.BOBMap.Map.Any V R P t → AnyM P (map {h = h} t)

module _ {K : Set ℓ} (V : Set ℓ') (R : OSet K) where
  open Map.BOBMap.Map {ℓ} {ℓ'} {K} (V) (R)
  open OSet R

  instance
    -- Assigning map functionallity to interface
    BOBMapImp : BMap {K = K} {V}
    BMap.Map BOBMapImp = Map V R 
    BMap.∅ BOBMapImp = map (leaf {{tt}})
    BMap._∈_ BOBMapImp k m = AnyM (λ kv' → k ≡ proj₁ kv') m
    --BMap.[_↦_]_ BOBMapImp k v m = AnyM (λ kv' → (k ≡ proj₁ kv') × (v ≡ proj₂ kv')) m
    BMap._∪_ BOBMapImp = {!!}
    BMap.lookup BOBMapImp (map m) = lookup m
    BMap.insert BOBMapImp (map m) kv = map $ proj₂ $ insert kv {{tt}} {{tt}} m  

    BMap.ip BOBMapImp (base , _) (map leaf) = base
    BMap.ip BOBMapImp (base , step) (map (node p ls rs bal)) = {!!} 

    BMap.ips BOBMapImp = {!!}

    BMap.lookup-∅ BOBMapImp = refl
    BMap.∈-∅ BOBMapImp {k} (map ())
      
    BMap.∈⇒lookup BOBMapImp {map Map.BOBMap.Map.leaf} ()
    BMap.∈⇒lookup BOBMapImp {map (node p lt rt bal)} {k} prf with compare k (proj₁ p)
    BMap.∈⇒lookup BOBMapImp {map (node p lt rt bal)} {k} prf
      | le with BMap.∈⇒lookup BOBMapImp {map ?} prf
    ... | x = map (left {!x!})
    BMap.∈⇒lookup BOBMapImp {map (node p lt rt bal)} {k} prf
      | eq = map (here refl)
    BMap.∈⇒lookup BOBMapImp {map (node p lt rt bal)} {k} prf
      | ge = {!!}
    BMap.lookup⇒∈ BOBMapImp = {!!}

    BMap.insert-∉ BOBMapImp {m} {k} {v} ¬x∈m = {!!}
    BMap.insert-∈ BOBMapImp k∈m v≢v' = {!!}

    BMap.ins-assoc BOBMapImp = {!!}
    BMap.ins-same BOBMapImp = {!!}
    BMap.∈-ins BOBMapImp = {!!}
    BMap.∪-assoc BOBMapImp = {!!}
    BMap.∪-∅ BOBMapImp = {!!}
    BMap.↦∈∪ BOBMapImp = {!!}
    BMap.equality BOBMapImp = {!!}
