module Map.BOBMapImp where

open import Prelude renaming (⊥ to ⊥'; ⊤ to ⊤')
open import OrdSet
open import Level using (Level; _⊔_)
open import Map.BasicMap
import Map.BOBMap
open import Data.Nat.Base using (ℕ)
open import Data.Product hiding (map)
open import Function.Base
open import Relation.Unary using (Pred)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality hiding (trans)
open import Data.Maybe.Base hiding (map)
open import Data.Sum hiding (map)
open import Relation.Nullary using (¬_)

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
  open OSet (ext {ℓ} {K} {R}) renaming 
   (_≺_ to _≺Ex_; trans to transEx; compare to compareEx; inreflex to inreflexEx)
  open OrdSet.ExtHelper {ℓ} {K} {R}

  liftMap : ∀ {l u : Ext K} {h : ℕ} → BOBMap (l , u) h → BOBMap (l , ⊤') h
  liftMap {l} {u} (leaf ⦃ l≤u ⦄) = leaf ⦃ maxEx {l} {u} l≤u ⦄
  liftMap (node p lm rm bal) = node p lm (liftMap rm) bal

  eqFromJust : ∀ {l : Level} {A : Set l} {a b : A} → just a ≡ just b → a ≡ b
  eqFromJust refl = refl
  
  instance
    -- Assigning map functionallity to interface
    BOBMapImp : BMap {K = K} {V}
    BMap.Map BOBMapImp = Map V R 
    BMap.∅ BOBMapImp = map (leaf {{tt}})
    BMap._↦_∈_ BOBMapImp k v m = AnyM (λ kv' → (k ≡ proj₁ kv') × (v ≡ proj₂ kv')) m
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
      | le = {!!} 
    BMap.∈⇒lookup BOBMapImp {map (node p lt rt bal)} {k} prf
      | eq = map (here (refl , (sym $ eqFromJust prf)))
    BMap.∈⇒lookup BOBMapImp {map (node p lt rt bal)} {k} prf
      | ge = {!!}
      
    BMap.lookup⇒∈ BOBMapImp {map (node p lt rt bal)} {.(proj₁ p)} (map (here (refl , refl))) with
      compare (proj₁ p) (proj₁ p)
    BMap.lookup⇒∈ BOBMapImp {map (node p lt rt bal)} {.(proj₁ p)} (map (here (refl , refl)))
      | inj₁ (! ⦃ prf ⦄) with (inreflex prf) refl
    ... | ()
    BMap.lookup⇒∈ BOBMapImp {map (node p lt rt bal)} {.(proj₁ p)} (map (here (refl , refl)))
      | eq = refl
    BMap.lookup⇒∈ BOBMapImp {map (node p lt rt bal)} {.(proj₁ p)} (map (here (refl , refl)))
      | inj₂ (inj₂ (! ⦃ prf ⦄)) with (inreflex prf) refl
    ... | () 
    BMap.lookup⇒∈ BOBMapImp {map (node p lt rt bal)} {k} (map (left prf)) = {!!}
    BMap.lookup⇒∈ BOBMapImp {map (node p lt rt bal)} {k} (map (right prf)) = {!!}
    
    BMap.insert-∉ BOBMapImp {map leaf} {k} {v} ¬x∈m with compare k k
    BMap.insert-∉ BOBMapImp {map Map.BOBMap.Map.leaf} {k} {v} ¬x∈m
      | inj₁ (! ⦃ prf ⦄) with (inreflex prf) refl
    ... | ()
    BMap.insert-∉ BOBMapImp {map Map.BOBMap.Map.leaf} {k} {v} ¬x∈m
      | eq = refl
    BMap.insert-∉ BOBMapImp {map Map.BOBMap.Map.leaf} {k} {v} ¬x∈m
      | inj₂ (inj₂ (! ⦃ prf ⦄)) with (inreflex prf) refl
    ... | ()
    BMap.insert-∉ BOBMapImp {map (node p lm rm bal)} {k} {v} ¬x∈m with compare k (proj₁ p) in cPrf 
    ... | le = {!!}
    ... | eq = {!!} 
    BMap.insert-∉ BOBMapImp {map (node p lm rm bal)} {k} {v} ¬x∈m
      | inj₂ (inj₂ (! ⦃ prf ⦄)) with insert (k , v) {{prf}} {{tt}} rm in prf'
    ... | 0# , rm' = {!!}
    ... | 1# , rm' = {!!}
    
    BMap.insert-∈ BOBMapImp k∈m v≢v' = {!!}

    BMap.ins-assoc BOBMapImp = {!!}
    BMap.ins-same BOBMapImp = {!!}
    BMap.∈-ins BOBMapImp = {!!}
    BMap.∪-assoc BOBMapImp = {!!}
    BMap.∪-∅ BOBMapImp = {!!}
    BMap.↦∈∪ BOBMapImp = {!!}

    -- REPLACE ALL OF THIS WITH A BETTER SOLUTION PLEASE END BY SUFFERING
    BMap.equality BOBMapImp {map leaf} {map leaf} prf = refl
    BMap.equality BOBMapImp {map leaf} {map (node p lt rt bal)} prf with
      compare (proj₁ p) (proj₁ p) | prf (proj₁ p)
    BMap.equality BOBMapImp {map leaf} {map (node p lt rt bal)} prf
      | inj₁ (! ⦃ prf' ⦄) | y with inreflex prf' refl
    ... | ()
    BMap.equality BOBMapImp {map leaf} {map (node p lt rt bal)} prf
      | eq | ()
    BMap.equality BOBMapImp {map leaf} {map (node p lt rt bal)} prf
      | inj₂ (inj₂ (! ⦃ prf' ⦄)) | y with inreflex prf' refl
    ... | ()
    -- replace following branch with a version using sym
    BMap.equality BOBMapImp {map (node p lt rt bal)} {map leaf} prf with
      compare (proj₁ p) (proj₁ p) | prf (proj₁ p)
    BMap.equality BOBMapImp {map (node p lt rt bal)} {map leaf} prf
      | inj₁ (! ⦃ prf' ⦄) | y with inreflex prf' refl
    ... | ()
    BMap.equality BOBMapImp {map (node p lt rt bal)} {map leaf} prf
      | eq | ()
    BMap.equality BOBMapImp {map (node p lt rt bal)} {map leaf} prf
      | inj₂ (inj₂ (! ⦃ prf' ⦄)) | y with inreflex prf' refl
    ... | () 
    BMap.equality BOBMapImp {map (node p lt rt bal)} {map (node p' lt' rt' bal')} prf with
      compare (proj₁ p) (proj₁ p) | compare (proj₁ p) (proj₁ p') | prf (proj₁ p)
    BMap.equality BOBMapImp {map (node p lt rt bal)} {map (node p' lt' rt' bal')} prf
      | inj₁ (! ⦃ prf' ⦄) | y | z with inreflex prf' refl
    ... | ()
    BMap.equality BOBMapImp {map (node p lt rt bal)} {map (node p' lt' rt' bal')} prf
      | inj₂ (inj₂ (! ⦃ prf' ⦄)) | y | z with inreflex prf' refl
    ... | ()
    BMap.equality BOBMapImp {map (node (fst , snd) lt rt bal)} {map (node p' lt' rt' bal')} prf
      | eq | inj₁ (! ⦃ prf' ⦄) | z = {!!}
    BMap.equality BOBMapImp {map (node (fst , snd) lt rt bal)} {map (node p' lt' rt' bal')} prf
      | eq | inj₂ (inj₂ (! ⦃ prf' ⦄)) | z = {!!}
    BMap.equality BOBMapImp {map (node (fst , snd) lt rt bal)} {map (node p' lt' rt' bal')} prf
      | eq | eq | z = {!!}
