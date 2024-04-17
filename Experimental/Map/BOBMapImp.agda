{-# OPTIONS --erasure #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet

module Map.BOBMapImp {k ℓ₁} (order : OrdSet k ℓ₁) where

open import Prelude
open import Level using (Level; _⊔_) renaming (suc to s; zero to z)
open import Data.Nat.Base using (ℕ; _*_; suc; zero)
open import Data.Product hiding (map)
open import Function.Base
open import Relation.Unary using (Pred)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality hiding (trans)
open import Data.Maybe.Base hiding (map)
open import Data.Sum hiding (map)
open import Relation.Nullary using (¬_)
open import Relation.Binary.Definitions


open import Map.BasicMap using (BMap)
open import Map.DeletableMap using (DMap)
open import Map.MergableMap using (MMap)
open import Map.CompleteMap using (CMap)
import Map.BOBMap order as BOB
open StrictTotalOrder (toStrictTotalOrder order) renaming (Carrier to Key)

open BOB

private
  variable
    ℓ ℓ' ℓₚ ℓₐ : Level

data AVLMap (V : Set ℓ') : Set (k ⊔ ℓ' ⊔ ℓ₁) where
  map : ∀ {h} → BOB.BOBMap V ⊥⁺ ⊤⁺ h → AVLMap V

data AnyM {V : Set ℓ'} (P : Pred V ℓₚ) (kₚ : Key) :
  AVLMap V → Set (k ⊔ ℓ₁ ⊔ ℓ' ⊔ ℓₚ) where
    map : ∀ {h t} → BOB.Any P kₚ t → AnyM P kₚ (map {h = h} t)

data AllM {V : Set ℓ'} (P : Pred (Key × V) ℓₐ) : AVLMap V → Set (k ⊔ ℓ₁ ⊔ ℓ' ⊔ ℓₐ) where
  map : ∀ {h t} → BOB.All P t → AllM P (map {h = h} t)

all∅ : {V : Set ℓ'} → (P : Pred (Key × V) ℓₐ) → AllM P (map (leaf {{⊥⁺<⊤⁺}}))
all∅ f = map (leaf ⦃ ⊥⁺<⊤⁺ ⦄)

module BMapAVLInstance (V : Set ℓ) where
  open import Map.Proofs.Insertion.Proofs order V
  open import Map.Proofs.Proofs order V as Proofs
  open import Map.Proofs.Deletion.Proofs order V
  open import Map.Proofs.Lookup.Proofs order V

  private
    height : AVLMap V → ℕ
    height (map {h} x) = h

    toBMap : (m : AVLMap V) → BOBMap V ⊥⁺  ⊤⁺ (height m)
    toBMap (map x) = x

    toAny : {m : AVLMap V} {P : Pred V ℓₚ} {k : Key} → AnyM P k m → Any P k (toBMap m)
    toAny (map x) = x

    toNotAny : {m : AVLMap V} {P : Pred V ℓₚ} {k : Key} → ¬ AnyM P k m → ¬ Any P k (toBMap m)
    toNotAny {m = (map m)} prf x = prf (map x)

    toNotAnyM : ∀ {h : ℕ} {m : BOBMap V ⊥⁺ ⊤⁺ h} {P : Pred V ℓₚ} {k : Key}
                → ¬ Any P k m → ¬ AnyM P k (map m)
    toNotAnyM neg (map prf) = neg prf

    fldr : {l : Level} {A : Set l} → (Key × V → A → A) → A → AVLMap V → A
    fldr f g (map m) = foldr f g m

    ¬Sym : ∀ {ℓ : Level} {A : Set ℓ} {a b : A} → ¬ (a ≡ b) → ¬ (b ≡ a)
    ¬Sym nEq x = nEq (sym x)

  instance
    ---------------------------------------------------------------------------------
    ---------------------------------------------------------------------------------
    -- BasicMap instance for AVLMap
    ---------------------------------------------------------------------------------
    ---------------------------------------------------------------------------------
    basicMap : BMap {ℓ₁ = ℓ₁} {K = Key} {V} (AVLMap V)
    ---------------------------------------------------------------------------------
    -- Assigning map functionality to interface
    ---------------------------------------------------------------------------------
    BMap.∅ basicMap = map (leaf {{⊥⁺<⊤⁺}})
    BMap._∈_ basicMap k m = AnyM {ℓₚ = z} (λ _ → True) k m
    BMap._↦_∈_ basicMap k v m = AnyM (λ v' → v ≡ v') k m
    BMap.lookup basicMap (map m) = lookup m
    BMap.lookup∈ basicMap (map prf) = lookup∈ prf
    BMap.insertWith basicMap k f (map m) = map (proj₂ $ insertWith k f {{⊥⁺<[ k ]}} {{[ k ]<⊤⁺}} m)

    ---------------------------------------------------------------------------------
    -- Relational properties
    ---------------------------------------------------------------------------------
    BMap.refl≐ basicMap = (λ k₁ v x₁ → x₁) , (λ k₁ v x₁ → x₁)
    BMap.sym≐ basicMap (α , β) = (λ k v x → β k v x ) , (λ k v x → α k v x)
    BMap.trans≐ basicMap (a , b) (c , d) = (λ k v x → c k v (a k v x)) , (λ k v x → b k v (d k v x))
    BMap.↦∈To∈ basicMap (map m) = map (↦∈To∈ m)

    ---------------------------------------------------------------------------------
    -- Insertion and lookup proofs
    ---------------------------------------------------------------------------------
    BMap.ips basicMap = {!!}
    BMap.lookup-∅ basicMap _ = refl
    BMap.∈↦-∅ basicMap _ _ (map ())
    BMap.∈-∅ basicMap _ (map ())
    BMap.∈⇒lookup basicMap (map m) k prf = map $ ∈⇒lookup m k prf
    BMap.lookup⇒∈ basicMap (map m) k v (map prf) = lookup⇒∈ k m prf
    BMap.lookup≡lookup∈ basicMap k (map m) (map prf) = lookup≡lookup∈ k ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ m prf
    BMap.mapsTo basicMap (map prf) = map (mapsTo prf)
    BMap.lookup-insert basicMap k (map m) f = lookup-insert k ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ m f
    BMap.ins-comm basicMap k k' v v' (map m) notEq =
      ( λ z v x → map (leftSide z v (toAny x)) ) , λ z v x → map (rightSide z v (toAny x))
      where
        l<k' : ⊥⁺ <⁺ BOB.[ k' ]
        l<k' = ⊥⁺<[ k' ]
        k'<u : BOB.[ k' ] <⁺ ⊤⁺
        k'<u = [ k' ]<⊤⁺
        l<k : ⊥⁺ <⁺ BOB.[ k ]
        l<k = ⊥⁺<[ k ]
        k<u : BOB.[ k ] <⁺ ⊤⁺
        k<u = [ k ]<⊤⁺
        leftSide : ∀ (z : Key) → (v'' : V)
          → z ↦ v'' ∈ proj₂ (insert (k , v) ⦃ l<k ⦄ ⦃ k<u ⦄ (proj₂ (insert (k' , v') ⦃ l<k' ⦄ ⦃ k'<u ⦄ m)))
          → z ↦ v'' ∈ proj₂ (insert (k' , v') ⦃ l<k' ⦄ ⦃ k'<u ⦄ (proj₂ (insert (k , v) ⦃ l<k ⦄ ⦃ k<u ⦄ m)))
        leftSide z v'' prf = insert-comm k k' z {v''} ⦃ l<k ⦄ ⦃ k<u ⦄ ⦃ l<k' ⦄ ⦃ k'<u ⦄ v v' m notEq prf
        rightSide : ∀ (z : Key) → (v'' : V)
          → z ↦ v'' ∈ proj₂ (insert (k' , v') ⦃ l<k' ⦄ ⦃ k'<u ⦄ (proj₂ (insert (k , v) ⦃ l<k ⦄ ⦃ k<u ⦄ m)))
          → z ↦ v'' ∈ proj₂ (insert (k , v) ⦃ l<k ⦄ ⦃ k<u ⦄ (proj₂ (insert (k' , v') ⦃ l<k' ⦄ ⦃ k'<u ⦄ m)))
        rightSide z v'' prf =
          insert-comm k' k z {v''} ⦃ l<k' ⦄ ⦃ k'<u ⦄ ⦃ l<k ⦄ ⦃ k<u ⦄ v' v m (¬Sym notEq) prf
    BMap.∈-ins basicMap (map m) k x v f (map prf) with ∈-ins k x f ⦃ ⊥⁺<[ k ] ⦄  ⦃ [ k ]<⊤⁺ ⦄ m prf
    ... | inj₁ x = inj₁ x
    ... | inj₂ y = inj₂ (map y)
    BMap.insert∈ basicMap k v (map m) = map (insert∈ k v ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ m)
    BMap.∈insert basicMap k (map m) (map prf) = insEq k ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ m prf
    BMap.insert-safe basicMap {k' = k'} (map prf) nEq =
      map (insert-safe ⦃ ⊥⁺<[ k' ] ⦄ ⦃ [ k' ]<⊤⁺ ⦄ prf nEq)

    ---------------------------------------------------------------------------------
    ---------------------------------------------------------------------------------
    -- DeletableMap instance for AVLMap
    ---------------------------------------------------------------------------------
    ---------------------------------------------------------------------------------
    deleteMap : DMap {ℓ₁ = ℓ₁} {K = Key} {V} (AVLMap V)
    ---------------------------------------------------------------------------------
    -- Assigning map functionality to interface
    ---------------------------------------------------------------------------------
    DMap.bMap deleteMap = basicMap
    DMap.delete deleteMap k (map m) = map (proj₂ $ delete k ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ m)

    ---------------------------------------------------------------------------------
    -- Deletion proofs
    ---------------------------------------------------------------------------------
    DMap.del-∉ deleteMap {k} {map m} prf = leftSide , rightSide
      where
        leftSide = λ k' v x → map $ del-∉del⊆ k ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ m (toNotAny prf) k' v (toAny x)
        rightSide = λ k' v x → map $ del-∉m⊆ k ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ m (toNotAny prf) k' v (toAny x)
    DMap.del-∈ deleteMap {k} {map m} prf = toNotAnyM $ del-∈ k m ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ (toAny prf)
    DMap.del-safe deleteMap {k} {k'} {m = map m} (map prf) nEq =
      map $ del-safe k k' m ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ prf nEq

    ---------------------------------------------------------------------------------
    ---------------------------------------------------------------------------------
    -- MergableMap instance for AVLMap
    ---------------------------------------------------------------------------------
    ---------------------------------------------------------------------------------
    mergeMap : MMap {ℓ₁ = ℓ₁} {K = Key} {V} (AVLMap V)
    MMap.bMap mergeMap = basicMap
    MMap.unionWith mergeMap f (map m) (map n) = map $ proj₂ (union f m n)
    MMap.∪-∅ᴸ mergeMap = {!!}
    MMap.∪-∅ᴿ mergeMap = {!!}
    MMap.∪-∅ mergeMap = {!!}
    MMap.∪-∈ mergeMap = {!!}
    MMap.∪-∈' mergeMap = {!!}

    BOBMapImp : CMap {ℓ₁ = ℓ₁} {K = Key} {V} (AVLMap V)
    CMap.dMap BOBMapImp = deleteMap
    CMap.mMap BOBMapImp = mergeMap

  allMLookup : ∀ {m : AVLMap V} {k : Key} {v : V} {P : Pred (Key × V) ℓₐ}
    → AnyM (_≡_ v) k m
    → AllM P m
    → P (k , v)
  allMLookup (map prf) (map all) = allLookup prf all

  allMInsert : ∀ {P : Pred (Key × V) ℓₐ} {(k , v) : Key × V} {m : AVLMap V}
    → P (k , v)
    → AllM P m
    → AllM P (BMap.insert basicMap k v m)
  allMInsert {P = P} {k , v} p (map m) = map $ allInsert ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ p m

-- -}
-- -}
-- -}
-- -}
