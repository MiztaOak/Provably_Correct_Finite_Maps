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

    BMap.lookup⇒∈ BOBMapImp (map m) k v (map prf) = lookup⇒∈ k m prf -- lookup⇒∈ k m prf

    BMap.lookup-insert BOBMapImp k (map m) f = lookup-insert k ⦃ ⊥⁺<[ k ] ⦄ ⦃ [ k ]<⊤⁺ ⦄ m f

    BMap.ins-comm BOBMapImp k k' f f' (map m) notEq =
      {! (λ k'' v x → map (ins-comm k k' ⦃ tt ⦄ ⦃ tt ⦄ ⦃ tt ⦄ ⦃ tt ⦄ f f' m notEq k'' v (toAny x))) ,
      λ k'' v x → map (ins-comm k' k ⦃ tt ⦄ ⦃ tt ⦄ ⦃ tt ⦄ ⦃ tt ⦄ f' f m (¬Sym notEq) k'' v (toAny x)) !}

{-      where
        ins-comm : ∀ {l u : Ext K} {h : ℕ}
                    → (k k' : K)
                    → {{l≤k : l ≺Ex # k}} {{k≤u : # k ≺Ex u}}
                    → {{l≤k' : l ≺Ex # k'}} {{k'≤u : # k' ≺Ex u}}
                    → (f f' : Maybe V → V)
                    → (m : BOBMap (l , u) h)
                    → k ≢ k'
                    → (∀ k'' v → k'' ↦ v ∈ proj₂ (insertWith k f (proj₂ (insertWith k' f' m)))
                      → k'' ↦ v ∈ proj₂ (insertWith k' f' (proj₂ (insertWith k f m))))
        ------ Leaf case
        ins-comm {l} k k' ⦃ o₁ ⦄ ⦃ o₂ ⦄ ⦃ o₃ ⦄ ⦃ o₄ ⦄ f f' (leaf ⦃ lu ⦄) nEq k'' v prf with
          insertWith {l} k f {{o₁}} {{o₂}} (leaf ⦃ lu ⦄)
        ... | _ , m with compare k' k
        ... | inj₁ (! ⦃ ord ⦄) with compareRight ord
        ... | x with compare k k'
        ... | ge with prf
        ... | here x = left ⦃ ord ⦄ (here ⦃ o₃ ⦄ ⦃ ord ⦄ x)
        ... | right (here x) = here ⦃ k≤u = o₂ ⦄ x
        ins-comm {l} k k' ⦃ o₁ ⦄ ⦃ o₂ ⦄ ⦃ o₃ ⦄ ⦃ o₄ ⦄ f f' (leaf ⦃ lu ⦄) nEq k'' v prf
          | _ , m | inj₂ (inj₂ (! ⦃ ord ⦄)) with compareLeft ord
        ... | x with compare k k'
        ... | le with prf
        ... | here x = right ⦃ ord ⦄ (here ⦃ ord ⦄ ⦃ o₄ ⦄ x)
        ... | left (here x) = here ⦃ o₁ ⦄ x
        ins-comm {l} k k' ⦃ o₁ ⦄ ⦃ o₂ ⦄ ⦃ o₃ ⦄ ⦃ o₄ ⦄ f f' (leaf ⦃ lu ⦄) nEq k'' v prf
          | _ , m | eq with nEq refl
        ... | ()

        ------ Node case
        ins-comm k k' ⦃ o₁ ⦄ ⦃ o₂ ⦄ ⦃ o₃ ⦄ ⦃ o₄ ⦄ f f' (node p lm rm b) nEq k'' v prf with
          compare k' (proj₁ p) in cK'
        -- k' ≺ (proj₁ p)
        ... | le with compare k (proj₁ p) in cK
        ... | le = {!!}
        ... | eq with compare k' (proj₁ p)
        ... | inj₁ (! ⦃ ord ⦄) with insertWith k' f' ⦃ p≤u = ord ⦄ lm in insK'
        ... | 0# , lm' = {!!}
        ... | 1# , lm' with b
        ... | ~+ = {!!}
        ... | ~0 = {!!}
        ... | ~- with insertWith k' f' ⦃ p≤u = ord ⦄ lm --THE FUCKING LOOP IS BACK OH DEAR GOD
        ... | 1# , lm'' = {!!}
        ins-comm k k' ⦃ o₁ ⦄ ⦃ o₂ ⦄ ⦃ o₃ ⦄ ⦃ o₄ ⦄ f f' (node p lm rm b) nEq k'' v prf
          | le | ge with insertWith k' f' lm
        ... | 1# , lm' = {!!}
        ... | 0# , lm' with compare k (proj₁ p)
        ... | inj₂ (inj₂ (! ⦃ ord ⦄)) with insertWith k f ⦃ ord ⦄ rm
        ... | 1# , rm' = {!!}
        ... | 0# , rm' = {!!}

        -- k' ≡ (proj₁ p)
        ins-comm k k' ⦃ o₁ ⦄ ⦃ o₂ ⦄ ⦃ o₃ ⦄ ⦃ o₄ ⦄ f f' (node p lm rm b) nEq k'' v prf
          | eq with compare k (proj₁ p)
        ... | le with insertWith k f lm
        ... | 0# , lm' with compareSelf (proj₁ p)
        ... | x with compare (proj₁ p) (proj₁ p)
        ... | eq = prf
        ins-comm k k' ⦃ o₁ ⦄ ⦃ o₂ ⦄ ⦃ o₃ ⦄ ⦃ o₄ ⦄ f f' (node p lm rm b) nEq k'' v prf
          | eq | le | 1# , lm' with b
        ... | ~+ with compareSelf (proj₁ p)
        ... | x with compare (proj₁ p) (proj₁ p)
        ... | eq = prf
        ins-comm k k' ⦃ o₁ ⦄ ⦃ o₂ ⦄ ⦃ o₃ ⦄ ⦃ o₄ ⦄ f f' (node p lm rm b) nEq k'' v prf
          | eq | le | 1# , lm' | ~0 with compareSelf (proj₁ p)
        ... | x with compare (proj₁ p) (proj₁ p)
        ... | eq = prf
        ins-comm k k' ⦃ o₁ ⦄ ⦃ o₂ ⦄ ⦃ o₃ ⦄ ⦃ o₄ ⦄ f f' (node p lm rm b) nEq k'' v prf
          | eq | le | 1# , lm' | ~- = {!!}
        ins-comm k k' ⦃ o₁ ⦄ ⦃ o₂ ⦄ ⦃ o₃ ⦄ ⦃ o₄ ⦄ f f' (node p lm rm b) nEq k'' v prf
          | eq | ge with insertWith k f rm
        ... | 1# , rm' with b
        ... | ~+ = {!!}
        ... | ~0 with compareSelf (proj₁ p)
        ... | x with compare (proj₁ p) (proj₁ p)
        ... | eq = prf
        ins-comm k k' ⦃ o₁ ⦄ ⦃ o₂ ⦄ ⦃ o₃ ⦄ ⦃ o₄ ⦄ f f' (node p lm rm b) nEq k'' v prf
          | eq | ge | 1# , rm' | ~- with compareSelf (proj₁ p)
        ... | x with compare (proj₁ p) (proj₁ p)
        ... | eq = prf
        ins-comm k k' ⦃ o₁ ⦄ ⦃ o₂ ⦄ ⦃ o₃ ⦄ ⦃ o₄ ⦄ f f' (node p lm rm b) nEq k'' v prf
          | eq | ge | 0# , rm' with compareSelf (proj₁ p)
        ... | x with compare (proj₁ p) (proj₁ p)
        ... | eq = prf
        ins-comm k k' ⦃ o₁ ⦄ ⦃ o₂ ⦄ ⦃ o₃ ⦄ ⦃ o₄ ⦄ f f' (node p lm rm b) nEq k'' v prf
          | eq | eq with nEq refl
        ... | ()

        -- k' ≻ (proj₁ p)
        ins-comm k k' ⦃ o₁ ⦄ ⦃ o₂ ⦄ ⦃ o₃ ⦄ ⦃ o₄ ⦄ f f' (node p lm rm b) nEq k'' v prf
          | ge with insertWith k' f' rm
        ... | 1# , n = {!!}
        ... | 0# , n with compare k (proj₁ p)
        ... | le = {!!}
        ... | ge = {!!}
        ... | eq = {!!} -}

    -- This proof can be written in a way better way using a helper for the recursion
    BMap.∈-ins BOBMapImp (map m) k x f (map prf) = {!!} -- with ∈-ins k x f {{tt}} {{tt}} m prf
{-      where
        lemma : ∀ {l u : Ext K} {h : ℕ} {i : ℕ₂}
                (m : BOBMap (l , u) h)
                {m' : BOBMap (l , u) (i ⊕ h)}
                {k x : K} (f : Maybe V → V)
                ⦃ @erased l≤k : l ≺Ex # k ⦄
                ⦃ @erased k≤u : # k ≺Ex u ⦄
                → insertWith k f m ≡ (i , m')
                → x ∈ m'
                → x ∈ proj₂ (insertWith k f m)
        lemma m f refl prf = prf

        ∈-ins : ∀ {l u : Ext K} {h : ℕ}
                (k x : K) (f : Maybe V → V)
                {{l≤k : l ≺Ex # k}} {{k≤u : # k ≺Ex u}}
                (m : BOBMap (l , u) h)
                → x ∈ (proj₂ (insertWith k f m))
                → (x ≡ k) ⊎ x ∈ m
        ∈-ins {l} {u} k x f {{l≤k}} {{k≤u}} leaf prf with
          insertWith {l} {u} k f {{l≤k}} {{k≤u}} leaf
        ... | 0# , leaf with prf
        ... | here tt = inj₁ refl
        ∈-ins {l} {u} k x f {{l≤k}} {{k≤u}} leaf prf
          | 1# , node p leaf leaf bal with prf
        ... | here tt = inj₁ refl
        ∈-ins k x f (node p lm rm bal) prf with compare k (proj₁ p)
        ... | le with insertWith k f lm in insK
        ... | 0# , lm' with prf
        ... | here _ = inj₂ (here tt)
        ... | right α = inj₂ (right α)
        ... | left α with ∈-ins k x f lm (lemma lm f insK α)
        ... | inj₁ eqP = inj₁ eqP
        ... | inj₂ anyP = inj₂ (left anyP)
        ∈-ins k x f (node p lm rm bal) prf
          | le | 1# , lm' with bal
        ... | ~+ with prf
        ... | here _ = inj₂ (here tt)
        ... | right α = inj₂ (right α)
        ... | left α with ∈-ins k x f lm (lemma lm f insK α)
        ... | inj₁ eqP = inj₁ eqP
        ... | inj₂ anyP = inj₂ (left anyP)
        ∈-ins k x f (node p lm rm bal) prf
          | le | 1# , lm' | ~0 with prf
        ... | here _ = inj₂ (here tt)
        ... | right α = inj₂ (right α)
        ... | left α with ∈-ins k x f lm (lemma lm f insK α)
        ... | inj₁ eqP = inj₁ eqP
        ... | inj₂ anyP = inj₂ (left anyP)
        ∈-ins k x f (node p lm rm bal) prf
          | le | 1# , lm' | ~- = {!!}
        ∈-ins k x f (node p lm rm bal) prf
          | eq with prf
        ... | here _ = inj₁ refl
        ... | left α = inj₂ (left α)
        ... | right α = inj₂ (right α)
        ∈-ins k x f (node p lm rm bal) prf
          | ge with insertWith k f rm in insK
        ... | 0# , rm' with prf
        ... | here _ = inj₂ (here tt)
        ... | left α = inj₂ (left α)
        ... | right α with ∈-ins k x f rm (lemma rm f insK α)
        ... | inj₁ eqP = inj₁ eqP
        ... | inj₂ anyP = inj₂ (right anyP)
        ∈-ins k x f (node p lm rm bal) prf
          | ge | 1# , rm' with bal
        ... | ~+ = {!!}
        ... | ~0 with prf
        ... | here _ = inj₂ (here tt)
        ... | left α = inj₂ (left α)
        ... | right α with ∈-ins k x f rm (lemma rm f insK α)
        ... | inj₁ eqP = inj₁ eqP
        ... | inj₂ anyP = inj₂ (right anyP)
        ∈-ins k x f (node p lm rm bal) prf
          | ge | 1# , rm' | ~- with prf
        ... | here _ = inj₂ (here tt)
        ... | left α = inj₂ (left α)
        ∈-ins k x f (node p lm rm bal) prf
          | ge | 1# , rm' | ~- | right α with ∈-ins k x f rm (lemma rm f insK α)
        ... | inj₁ eqP = inj₁ eqP
        ... | inj₂ anyP = inj₂ (right anyP)
    ... | inj₁ e = inj₁ e
    ... | inj₂ r = inj₂ (map r)
-}
    BMap.insert∈ BOBMapImp k v (map m) = {!!} {- map (insert∈ k v ⦃ tt ⦄ ⦃ tt ⦄ m) -}
    {-  where
        insert∈ : ∀ {l u : Ext K} {h : ℕ} → (k : K) → (v : V)
                  {{l≤p : l ≺Ex # k}} {{p≤u : # k ≺Ex u}}
                  → (m : BOBMap (l , u) h)
                  → k ↦ v ∈ (proj₂ $ insertWith k (λ _ → v) m)
        insert∈ k v leaf = here refl
        insert∈ k v (node p lm rm bal) with compare k (proj₁ p)
        insert∈ k v (node p lm rm bal)
          | le with insert∈ k v lm
        ... | x with insertWith k (λ _ → v) lm
        ... | 0# , _ = left x
        ... | 1# , lm' with bal
        ... | ~+ = left x
        ... | ~0 = left x
        ... | ~- = anyRotRᴸ p lm' rm x
        insert∈ k v (node p lm rm bal)
          | eq = here refl
        insert∈ k v (node p lm rm bal)
          | ge with insert∈ k v rm
        ... | x with insertWith k (λ _ → v) rm
        ... | 0# , _ = right x
        ... | 1# , rm' with bal
        ... | ~+ = anyRotLᴿ p lm rm' x
        ... | ~0 = right x
        ... | ~- = right x
-}
    BMap.insert-safe BOBMapImp (map prf) nEq = {! map (noAlterInsert {{tt}} {{tt}} prf nEq) !}
      {-where
        noAlterInsert : {k k' : K} {v v' : V} {l u : Ext K} {h : ℕ}
                        {{l≤k' : l ≺Ex # k'}} {{k'≤u : # k' ≺Ex u}}
                        {m : BOBMap (l , u) h}
                        → k ↦ v ∈ m → ¬ (k ≡ k')
                        → k ↦ v ∈ proj₂ (insert (k' , v') m)
        noAlterInsert {k} {k'} (here x {lm} {rm} {bal}) nEq with compare k' k
        noAlterInsert {k} {k'} {v' = v'} (here x {lm} {rm} {bal}) nEq
          | le with insertWith k' (λ _ → v') lm
        ... | 0# , lm' = here x
        ... | 1# , lm' with bal
        ... | ~+ = here x
        ... | ~0 = here x
        ... | ~- = {!!}
        noAlterInsert {k} {k'} {v' = v'} (here x {lm} {rm} {bal}) nEq
          | ge with insertWith k' (λ _ → v') rm
        ... | 0# , rm' = here x
        ... | 1# , rm' with bal
        ... | ~+ = {!!}
        ... | ~0 = here x
        ... | ~- = here x
        noAlterInsert {k} {k'} (here x {lm} {rm} {bal}) nEq
          | eq with nEq refl
        ... | ()
        noAlterInsert {k} {k'} {v} {v'} {{l≤k'}} {m = node p _ _ b} (left {lm = lm} ⦃ k≺k' ⦄ prf {rm}) nEq
          with compare k' (proj₁ p)
        ... | le with insertWith k' (λ _ → v') lm in insL
        ... | 0# , lm' with noAlterInsert {v' = v'} prf nEq
        ... | prf' with proj₂ (insertWith k' (λ _ → v') lm)
        ... | lm'' = left {!!}
        noAlterInsert {k} {k'} {v} {v'} {{l≤k'}} {m = node p _ _ b} (left {lm = lm} ⦃ k≺k' ⦄ prf {rm}) nEq
          | le | 1# , lm' = {!!}
        noAlterInsert {k} {k'} {v} {v'} {{l≤k'}} {m = node p _ _ b} (left {lm = lm} ⦃ k≺k' ⦄ prf {rm}) nEq
          | eq = left prf
        noAlterInsert {k} {k'} {v} {v'} {{l≤k'}} {m = node p _ _ b} (left {lm = lm} ⦃ k≺k' ⦄ prf {rm}) nEq
          | ge with insertWith k' (λ _ → v') rm
        ... | 0# , rm' = left prf
        ... | 1# , rm' with b
        ... | ~+ = anyRotLᴸ p lm rm' prf
        ... | ~0 = left prf
        ... | ~- = left prf
        noAlterInsert {k} {k'} {v} {v'} (right prf) nEq = {!!}
-}

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
