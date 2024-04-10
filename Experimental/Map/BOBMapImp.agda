{-# OPTIONS --erasure #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet

module Map.BOBMapImp {k ℓ₁} (order : OrdSet k ℓ₁) where

open import Prelude
open import Level using (Level; _⊔_) renaming (suc to s; zero to z)
open import Map.BasicMap using (BMap)
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


module BMapAVLInstance (V : Set ℓ) where
  open import Map.Proofs.InsertionProofs order V as insP
  open import Map.Proofs.Proofs order V as Proofs
  open import Map.Proofs.DeletionProofs order V

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
    -- Assigning map functionality to interface
    ---------------------------------------------------------------------------------
    BOBMapImp : BMap {ℓ₁ = ℓ₁} {K = Key} {V}
    BMap.Map BOBMapImp = AVLMap V
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
        bobP : (AVLMap V → Set (k ⊔ ℓ)) → (∀ {h : ℕ} → BOBMap V ⊥⁺ ⊤⁺ h → Set (k ⊔ ℓ))
        bobP P m = P (map m)

    BMap.lookup-∅ BOBMapImp _ = refl
    BMap.∈↦-∅ BOBMapImp k v (map ())

    BMap.∈-∅ BOBMapImp _ (map ())

    BMap.∈⇒lookup BOBMapImp (map m) k prf = map $ insP.∈⇒lookup m k prf

    BMap.lookup⇒∈ BOBMapImp (map m) k v (map prf) = insP.lookup⇒∈ k m prf

    BMap.lookup-insert BOBMapImp k (map m) f = insP.lookup-insert k ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ m f

    BMap.ins-comm BOBMapImp k k' v v' (map m) notEq =
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
       rightSide z v'' prf = insert-comm k' k z {v''} ⦃ l<k' ⦄ ⦃ k'<u ⦄ ⦃ l<k ⦄ ⦃ k<u ⦄ v' v m (¬Sym notEq) prf

    BMap.∈-ins BOBMapImp (map m) k x v f (map prf) with ∈-ins k x f ⦃ ⊥⁺<[ k ] ⦄  ⦃ [ k ]<⊤⁺ ⦄ m prf
    ... | inj₁ x = inj₁ x
    ... | inj₂ y = inj₂ (map y)

    BMap.insert∈ BOBMapImp k v (map m) = map (insert∈ k v ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ m)

    BMap.∈insert BOBMapImp k (map m) (map prf) = insEq k ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ m prf

    BMap.insert-safe BOBMapImp {k' = k'} (map prf) nEq =
      map (insert-safe ⦃ ⊥⁺<[ k' ] ⦄ ⦃ [ k' ]<⊤⁺ ⦄ prf nEq)

    ---------------------------------------------------------------------------------
    -- Union proofs
    ---------------------------------------------------------------------------------
    proj₁ (BMap.∪-∅ᴸ BOBMapImp (map leaf) f) k v (map ())
    proj₁ (BMap.∪-∅ᴸ BOBMapImp (map (node _ _ _ _)) f) k v prf = prf
    proj₂ (BMap.∪-∅ᴸ BOBMapImp (map leaf) f) k v (map ())
    proj₂ (BMap.∪-∅ᴸ BOBMapImp (map (node _ _ _ _)) f) k v prf = prf
    proj₁ (BMap.∪-∅ᴿ BOBMapImp m f) k v prf = prf
    proj₂ (BMap.∪-∅ᴿ BOBMapImp m f) k v prf = prf
    -- hmm shoud this be removed or?
    BMap.∪-∅ BOBMapImp m f = (proj₁ $ BMap.∪-∅ᴸ BOBMapImp m f) , (proj₂ $ BMap.∪-∅ᴸ BOBMapImp m f)

    BMap.∪-∈ BOBMapImp (map leaf) (map leaf) f k (map ())
    BMap.∪-∈ BOBMapImp (map leaf) (map m@(node _ _ _ _)) f k prf = inj₂ prf
    BMap.∪-∈ BOBMapImp (map n@(node _ _ _ _)) (map leaf) f k prf = inj₁ prf
    BMap.∪-∈ BOBMapImp (map n@(node _ _ _ _)) (map m@(node p l r _)) f k prf = {!!}
    {-with (find k n , find k m)
      where
        find : ∀ {l u h} (x : Key)
               → (a : BOBMap V l u h)
               → Maybe (x ∈ a)
        find x leaf = nothing
        find x (node p lt rt bal) with compare x (proj₁ p)
        ... | tri< a _ _ = (find x lt) >>= λ α → just (left ⦃ [ a ]ᴿ ⦄ α)
        ... | tri≈ _ refl _ = just $ here ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ tt
        ... | tri> _ _ c = (find x rt) >>= λ α → just (right ⦃ [ c ]ᴿ ⦄ α)
    ... | just α , just β = inj₁ (map α)
    ... | just α , nothing = inj₁ (map α)
    ... | nothing , just β = inj₂ (map β)
    ... | nothing , nothing = {!!} -}

    BMap.∪-∈' BOBMapImp (map leaf) m f k (inj₁ (map ()))
    BMap.∪-∈' BOBMapImp (map (node _ _ _ _)) (map leaf) f k (inj₁ prf) = prf
    BMap.∪-∈' BOBMapImp (map (node _ _ _ _)) (map (node _ _ _ _)) f k (inj₁ prf) = {!!}
    BMap.∪-∈' BOBMapImp n (map leaf) f k (inj₂ (map ()))
    BMap.∪-∈' BOBMapImp (map leaf) (map (node _ _ _ _)) f k (inj₂ prf) = prf
    BMap.∪-∈' BOBMapImp (map (node _ _ _ _)) (map (node _ _ _ _)) f k (inj₂ prf) = {!!}

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

  allMLookup : ∀ {m : AVLMap V} {k : Key} {v : V} {P : Pred (Key × V) ℓₐ}
    → AnyM (_≡_ v) k m
    → AllM P m
    → P (k , v)
  allMLookup (map prf) (map all) = allLookup prf all

  allMInsert : ∀ {P : Pred (Key × V) ℓₐ} {(k , v) : Key × V} {m : AVLMap V}
    → P (k , v)
    → AllM P m
    → AllM P (BMap.insert BOBMapImp k v m)
  allMInsert {P = P} {k , v} p (map m) = map $ allInsert ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ p m

-- -}
-- -}
-- -}
-- -}
