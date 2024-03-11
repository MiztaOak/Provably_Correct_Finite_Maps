{-# OPTIONS --erasure #-}
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet

module Map.BOBMapImp {k ℓ₁} (order : OrdSet k ℓ₁) where

open import Prelude
open import Level using (Level; _⊔_) renaming (suc to s; zero to z)
open import Map.BasicMap
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

import Map.BOBMap order as BOB
open StrictTotalOrder (toStrictTotalOrder order) renaming (Carrier to Key)

open BOB hiding (max) public

private
  variable
    ℓ ℓ' ℓₚ : Level

data Map (V : Set ℓ') : Set (k ⊔ ℓ' ⊔ ℓ₁) where
  map : ∀ {h} → BOB.BOBMap V ⊥⁺ ⊤⁺ h → Map V

data AnyM {V : Set ℓ'} (P : Pred V ℓₚ) (kₚ : Key) :
  Map V → Set (k ⊔ ℓ₁ ⊔ ℓ' ⊔ ℓₚ) where
    map : ∀ {h t} → BOB.Any P kₚ t → AnyM P kₚ (map {h = h} t)

module _ (V : Set ℓ) where
  open import Map.Proofs.InsertionProofs order V

  private
    height : Map V → ℕ
    height (map {h} x) = h

    toBMap : (m : Map V) → BOBMap V ⊥⁺  ⊤⁺ (height m)
    toBMap (map x) = x

    toAny : {m : Map V} {P : Pred V ℓₚ} {k : Key} → AnyM P k m → Any P k (toBMap m)
    toAny (map x) = x

    toNotAny : {m : Map V} {P : Pred V ℓₚ} {k : Key} → ¬ AnyM P k m → ¬ Any P k (toBMap m)
    toNotAny {m = (map m)} prf x = prf (map x)

    fldr : {l : Level} {A : Set l} → (Key × V → A → A) → A → Map V → A
    fldr f g (map m) = foldr f g m

    ¬Sym : ∀ {ℓ : Level} {A : Set ℓ} {a b : A} → ¬ (a ≡ b) → ¬ (b ≡ a)
    ¬Sym nEq x = nEq (sym x)

  instance
    ---------------------------------------------------------------------------------
    -- Assigning map functionality to interface
    ---------------------------------------------------------------------------------
    BOBMapImp : BMap {ℓ₁ = ℓ₁} {K = Key} {V}
    BMap.Map BOBMapImp = Map V
    BMap.∅ BOBMapImp = map (leaf {{⊥⁺<⊤⁺}})

    BMap._∈_ BOBMapImp k m = AnyM {ℓₚ = z} (λ _ → True) k m
    BMap._↦_∈_ BOBMapImp k v m = AnyM (λ v' → v ≡ v') k m

    BMap.unionWith BOBMapImp _ (map leaf) m = m
    BMap.unionWith BOBMapImp _ n (map leaf) = n
    BMap.unionWith BOBMapImp f n m =
      fldr (λ (k , v) t → map $ proj₂ $ insertWith k (f v) {{⊥⁺<[ k ]}} {{[ k ]<⊤⁺}} (toBMap t)) m n

    BMap.lookup BOBMapImp (map m) = lookup m
    BMap.lookup∈ BOBMapImp (map prf) = lookup∈ prf

    BMap.insertWith BOBMapImp k f (map x) = map (proj₂ $ insertWith k f {{⊥⁺<[ k ]}} {{[ k ]<⊤⁺}} x)

    BMap.delete BOBMapImp k (map m) = map (proj₂ $ delete k ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ m)

    ---------------------------------------------------------------------------------
    -- Relational properties
    ---------------------------------------------------------------------------------
    BMap.refl≐ BOBMapImp = (λ k₁ v x₁ → x₁) , (λ k₁ v x₁ → x₁)

    BMap.sym≐ BOBMapImp (α , β) = (λ k v x → β k v x ) , (λ k v x → α k v x)

    BMap.trans≐ BOBMapImp (a , b) (c , d) = (λ k v x → c k v (a k v x)) , (λ k v x → b k v (d k v x))

    BMap.↦∈To∈ BOBMapImp (map x) = map (↦∈To∈ x)

    ---------------------------------------------------------------------------------
    -- Insertion and lookup proofs
    ---------------------------------------------------------------------------------
    -- Leaving these for later as we are not 100% sure that they are relevant or correct
    BMap.ips BOBMapImp = {!!}

    BMap.lookup-∅ BOBMapImp _ = refl
    BMap.∈↦-∅ BOBMapImp k v (map ())

    BMap.∈-∅ BOBMapImp _ (map ())

    BMap.∈⇒lookup BOBMapImp (map m) k prf = map $ ∈⇒lookup m k prf

    BMap.lookup⇒∈ BOBMapImp (map m) k v (map prf) = lookup⇒∈ k m prf

    BMap.lookup-insert BOBMapImp k (map m) f = lookup-insert k ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ m f

    BMap.ins-comm BOBMapImp k k' f f' (map m) notEq = {!!}
{-      where
        x = λ k'' v x → map (
          ins-comm k k' ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ ⦃ ⊥⁺<[ k' ] ⦄ ⦃ [ k' ]<⊤⁺ ⦄ f f' m notEq k'' v (toAny x))
        y = λ k'' v x → map (
          ins-comm k' k ⦃ ⊥⁺<[ k' ] ⦄ ⦃ [ k' ]<⊤⁺ ⦄ ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ f' f m (¬Sym notEq) k'' v (toAny x))
-}
    BMap.∈-ins BOBMapImp (map m) k x f (map prf) with ∈-ins k x f ⦃ ⊥⁺<[ k ] ⦄  ⦃ [ k ]<⊤⁺ ⦄ m prf
    ... | inj₁ x = inj₁ x
    ... | inj₂ y = inj₂ (map y)

    BMap.insert∈ BOBMapImp k v (map m) = map (insert∈ k v ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ m)

    BMap.insert-safe BOBMapImp {k' = k'} (map prf) nEq =
      map (insert-safe ⦃ ⊥⁺<[ k' ] ⦄ ⦃ [ k' ]<⊤⁺ ⦄ prf nEq)

    ---------------------------------------------------------------------------------
    -- Union proofs
    ---------------------------------------------------------------------------------
    BMap.∪-∅ᴸ BOBMapImp m f = {!!}
    BMap.∪-∅ᴿ BOBMapImp m f = {!!}
    BMap.∪-∅ BOBMapImp m f = {!!}

    BMap.∪-∈ BOBMapImp (map n) (map m) f k prf = {!!} {- with (find k n , find k m)
      where
        find : ∀ {l u h} (x : K)
               → (a : BOBMap (l , u) h)
               → Maybe (x ∈ a)
        find x leaf = nothing
        find x (node p lt rt bal) with compare x (proj₁ p)
        ... | le = (find x lt) >>= λ α → just (left α)
        ... | eq = just $ here {{mapOrd lt}} {{mapOrd rt}} tt
        ... | ge = (find x rt) >>= λ α → just (right α)
    ... | just α , just β = inj₁ (map α)
    ... | just α , nothing = inj₁ (map α)
    ... | nothing , just β = inj₂ (map β)
    ... | nothing , nothing = {!!} -}

    BMap.∪-∈' BOBMapImp n m f k (inj₁ prf) = {!!}
    BMap.∪-∈' BOBMapImp n m f k (inj₂ prf) = {!!}

    ---------------------------------------------------------------------------------
    -- Deletion proofs
    ---------------------------------------------------------------------------------
    BMap.del-∉ BOBMapImp prf = {!!}

    BMap.del-∈ BOBMapImp prf = {!!}

    BMap.del-safe BOBMapImp prf nEq = {!!}
-- -}
-- -}
-- -}
-- -}
