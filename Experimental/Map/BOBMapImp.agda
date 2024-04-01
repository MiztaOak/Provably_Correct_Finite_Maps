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
  open import Map.Proofs.Proofs order V
  open import Map.Proofs.DeletionProofs order V

  private
    height : Map V → ℕ
    height (map {h} x) = h

    toBMap : (m : Map V) → BOBMap V ⊥⁺  ⊤⁺ (height m)
    toBMap (map x) = x

    toAny : {m : Map V} {P : Pred V ℓₚ} {k : Key} → AnyM P k m → Any P k (toBMap m)
    toAny (map x) = x

    toNotAny : {m : Map V} {P : Pred V ℓₚ} {k : Key} → ¬ AnyM P k m → ¬ Any P k (toBMap m)
    toNotAny {m = (map m)} prf x = prf (map x)

    toNotAnyM : ∀ {h : ℕ} {m : BOBMap V ⊥⁺ ⊤⁺ h} {P : Pred V ℓₚ} {k : Key}
                → ¬ Any P k m → ¬ AnyM P k (map m)
    toNotAnyM neg (map prf) = neg prf

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
    BMap.ips BOBMapImp P (base , step) (map m) = ip-insert (bobP P) ((λ leaf → {!base!}) , {!!}) m
      where
        bobP : (Map V → Set (k ⊔ ℓ)) → (∀ {h : ℕ} → BOBMap V ⊥⁺ ⊤⁺ h → Set (k ⊔ ℓ))
        bobP P m = P (map m)

    BMap.lookup-∅ BOBMapImp _ = refl
    BMap.∈↦-∅ BOBMapImp k v (map ())

    BMap.∈-∅ BOBMapImp _ (map ())

    BMap.∈⇒lookup BOBMapImp (map m) k prf = map $ ∈⇒lookup m k prf

    BMap.lookup⇒∈ BOBMapImp (map m) k v (map prf) = lookup⇒∈ k m prf

    BMap.lookup-insert BOBMapImp k (map m) f = lookup-insert k ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ m f

    BMap.ins-comm BOBMapImp k k' f f' (map m) notEq =
      (λ z v x → map (leftSide z (toAny x))) , λ z v x → map (rightSide z (toAny x))
      where
       l<k' : ⊥⁺ <⁺ BOB.[ k' ]
       l<k' = ⊥⁺<[ k' ]
       k'<u : BOB.[ k' ] <⁺ ⊤⁺
       k'<u = [ k' ]<⊤⁺
       l<k : ⊥⁺ <⁺ BOB.[ k ]
       l<k = ⊥⁺<[ k ]
       k<u : BOB.[ k ] <⁺ ⊤⁺
       k<u = [ k ]<⊤⁺
       leftSide : ∀ (z : Key) → {v : V}
         → z ↦ v ∈ proj₂ (insertWith k f ⦃ l<k ⦄ ⦃ k<u ⦄ (proj₂ (insertWith k' f' ⦃ l<k' ⦄ ⦃ k'<u ⦄ m)))
         → z ↦ v ∈ proj₂ (insertWith k' f' ⦃ l<k' ⦄ ⦃ k'<u ⦄ (proj₂ (insertWith k f ⦃ l<k ⦄ ⦃ k<u ⦄ m)))
       leftSide z prf = ins-comm k k' z ⦃ l<k ⦄ ⦃ k<u ⦄ ⦃ l<k' ⦄ ⦃ k'<u ⦄ f f' m notEq prf
       rightSide : ∀ (z : Key) → {v : V}
         → z ↦ v ∈ proj₂ (insertWith k' f' ⦃ l<k' ⦄ ⦃ k'<u ⦄ (proj₂ (insertWith k f ⦃ l<k ⦄ ⦃ k<u ⦄ m)))
         → z ↦ v ∈ proj₂ (insertWith k f ⦃ l<k ⦄ ⦃ k<u ⦄ (proj₂ (insertWith k' f' ⦃ l<k' ⦄ ⦃ k'<u ⦄ m)))
       rightSide z prf = ins-comm k' k z ⦃ l<k' ⦄ ⦃ k'<u ⦄ ⦃ l<k ⦄ ⦃ k<u ⦄ f' f m (¬Sym notEq) prf

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
    BMap.del-∉ BOBMapImp {k} {map m} prf = leftSide , rightSide
      where
        leftSide = λ k' v x → map $ del-∉del⊆ k ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ m (toNotAny prf) k' v (toAny x)
        rightSide = λ k' v x → map $ del-∉m⊆ k ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ m (toNotAny prf) k' v (toAny x)

    BMap.del-∈ BOBMapImp {k} {map m} prf = toNotAnyM $ del-∈ k m ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ (toAny prf)

    BMap.del-safe BOBMapImp {k} {k'} {m = map m} (map prf) nEq =
      map $ del-safe k k' m ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ prf nEq
-- -}
-- -}
-- -}
-- -}
