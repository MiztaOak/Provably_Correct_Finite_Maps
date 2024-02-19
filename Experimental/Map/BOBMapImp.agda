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

  private
    height : Map V R → ℕ
    height (map {h} x) = h

    toBMap : (m : Map V R) → BOBMap (⊥' , ⊤') (height m)
    toBMap (map x) = x

    toAny : {m : Map V R} {P : Pred (K × V) ℓₚ} → AnyM P m → Any P (toBMap m)
    toAny (map x) = x

    fldr : {l : Level} {A : Set l} → (K × V → A → A) → A → Map V R → A
    fldr f g (map m) = foldr f g m

    liftMap : ∀ {l u : Ext K} {h : ℕ} → BOBMap (l , u) h → BOBMap (l , ⊤') h
    liftMap {l} {u} (leaf ⦃ l≤u ⦄) = leaf ⦃ maxEx {l} {u} l≤u ⦄
    liftMap (node p lm rm bal) = node p lm (liftMap rm) bal

    eqFromJust : ∀ {l : Level} {A : Set l} {a b : A} → just a ≡ just b → a ≡ b
    eqFromJust refl = refl

    _↦_∈_ : K → V → {l u : Ext K} {h : ℕ} → BOBMap (l , u) h → Set (ℓ ⊔ ℓ')
    k ↦ v ∈ m = Any (λ kv' → (k ≡ proj₁ kv') × (v ≡ proj₂ kv')) m

    _∈_ : K → {l u : Ext K} {h : ℕ} → BOBMap (l , u) h → Set (ℓ ⊔ ℓ')
    k ∈ m = Any (λ kv' → (k ≡ proj₁ kv')) m

    _⊆_ : {l u : Ext K} {h h' : ℕ} → BOBMap (l , u) h → BOBMap (l , u) h' → Set (ℓ ⊔ ℓ')
    n ⊆ m = ∀ k v → k ↦ v ∈ n → k ↦ v ∈ m

    _≐_ : {l u : Ext K} {h h' : ℕ} → BOBMap (l , u) h → BOBMap (l , u) h' → Set (ℓ ⊔ ℓ')
    n ≐ m = (n ⊆ m) × (m ⊆ n)

  instance
    -- Assigning map functionality to interface
    BOBMapImp : BMap {K = K} {V}
    BMap.Map BOBMapImp = Map V R
    BMap.∅ BOBMapImp = map (leaf {{tt}})
    BMap._∈_ BOBMapImp k m = AnyM (λ kv' → (k ≡ proj₁ kv')) m
    BMap._↦_∈_ BOBMapImp k v m = AnyM (λ kv' → (k ≡ proj₁ kv') × (v ≡ proj₂ kv')) m
    BMap.unionWith BOBMapImp f n m =
      fldr (λ (k , v) t → map $ proj₂ $ insertWith k (f v) {{tt}} {{tt}} (toBMap t)) m n
    BMap.lookup BOBMapImp (map m) = lookup m
    BMap.insertWith BOBMapImp k f (map x) = map $ proj₂ $ insertWith k f {{tt}} {{tt}} x

    -- Leaving these for later as we are not 100% sure that they are relevant or correct
    BMap.ip BOBMapImp _ (base , _) (map leaf) = base
    BMap.ip BOBMapImp P (base , step) (map (node p ls rs bal)) = {!!}
    BMap.ips BOBMapImp = {!!}

    BMap.lookup-∅ BOBMapImp _ = refl
    BMap.∈↦-∅ BOBMapImp k v (map ())

    BMap.∈-∅ BOBMapImp _ (map ())

    BMap.∈⇒lookup BOBMapImp (map m) k prf = map $ ∈⇒lookup m k prf
      where
        ∈⇒lookup : ∀ {l u : Ext K} {h : ℕ} (m : BOBMap (l , u) h) (k : K) {v : V}
                   → lookup m k ≡ just v
                   → k ↦ v ∈ m
        ∈⇒lookup (node p lm rm bal) k prf with compare k (proj₁ p)
        ... | le = left (∈⇒lookup lm k prf)
        ... | eq = here (refl , (sym $ eqFromJust prf))
        ... | ge = right (∈⇒lookup rm k prf)

    -- Needs a connection between the branches of any and compare to solve
    -- might be some cleaver way to deduce k's relation to the map using
    -- left and right
    BMap.lookup⇒∈ BOBMapImp (map m) k v (map prf) = lookup⇒∈ k m prf
      where
        lookup⇒∈ : ∀ {l u : Ext K} {h : ℕ} (k : K) {v : V} (m : BOBMap (l , u) h)
                   → k ↦ v ∈ m
                   → lookup m k ≡ just v
        lookup⇒∈ k (node p lm rm bal) (left prf) with compare k (proj₁ p)
        ... | le = lookup⇒∈ k lm prf
        ... | eq = {!!}
        ... | ge = {!!}
        lookup⇒∈ k (node p lm rm bal) (right prf) with compare k (proj₁ p)
        ... | le = {!!}
        ... | eq = {!!}
        ... | ge = lookup⇒∈ k rm prf
        lookup⇒∈ (.(proj₁ p)) (node p lm rm bal) (here (refl , refl))
          with compare (proj₁ p) (proj₁ p)
        lookup⇒∈ (.(proj₁ p)) (node p lm rm bal) (here (refl , refl))
          | inj₁ (! ⦃ prf ⦄) with inreflex prf refl
        ... | ()
        lookup⇒∈ (.(proj₁ p)) (node p lm rm bal) (here (refl , refl))
          | eq = refl
        lookup⇒∈ (.(proj₁ p)) (node p lm rm bal) (here (refl , refl))
          | inj₂ (inj₂ (! ⦃ prf ⦄)) with inreflex prf refl
        ... | ()

    BMap.lookup-insert∈ BOBMapImp k∈m (map x) k v = {!!}

    BMap.lookup-insert∉ BOBMapImp k∉m (map x) k v = {!!}

    BMap.ins-comm BOBMapImp = {!!}
    BMap.∈-ins BOBMapImp = {!!}
    BMap.∪-assoc BOBMapImp = {!!}
    BMap.∪-∅ BOBMapImp = {!!}
    BMap.∪-∈ BOBMapImp = {!!}

    BMap.eq? BOBMapImp f g fn
      = (λ k v _ → proj₂ (fn k v)) , λ k v _ → proj₁ (fn k v)
    BMap.eq∈ BOBMapImp = {!!}
