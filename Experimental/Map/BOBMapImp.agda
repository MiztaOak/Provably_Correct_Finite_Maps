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

    toNotAny : {m : Map V R} {P : Pred (K × V) ℓₚ} → ¬ AnyM P m → ¬ Any P (toBMap m)
    toNotAny {m = (map m)} prf x = prf (map x)

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

    _∉_ : K → {l u : Ext K} {h : ℕ} → BOBMap (l , u) h → Set (ℓ ⊔ ℓ')
    k ∉ m = ¬ (k ∈ m)

    _⊆_ : {l u : Ext K} {h h' : ℕ} → BOBMap (l , u) h → BOBMap (l , u) h' → Set (ℓ ⊔ ℓ')
    n ⊆ m = ∀ k v → k ↦ v ∈ n → k ↦ v ∈ m

    _≐_ : {l u : Ext K} {h h' : ℕ} → BOBMap (l , u) h → BOBMap (l , u) h' → Set (ℓ ⊔ ℓ')
    n ≐ m = (n ⊆ m) × (m ⊆ n)

    ¬Left : ∀ {l u : Ext K} {hl hr h : ℕ} {P : Pred (K × V) ℓₚ} {k : K } {v : V}
              {lm : BOBMap (l , # k) hl} {rm : BOBMap (# k , u) hr}
              {bal : hl ~ hr ⊔ h}
              → ¬ (Any P (node (k , v) lm rm bal)) → ¬ (Any P lm)
    ¬Left prf lmP = prf (left lmP)

    ¬Right : ∀ {l u : Ext K} {hl hr h : ℕ} {P : Pred (K × V) ℓₚ} {k : K} {v : V}
               {lm : BOBMap (l , # k) hl} {rm : BOBMap (# k , u) hr}
               {bal : hl ~ hr ⊔ h}
               → ¬ (Any P (node (k , v) lm rm bal))
               → ¬ (Any P rm)
    ¬Right prf rmP = prf (right rmP)

    compareSelf : ∀ (k : K) → compare k k ≡ eq
    compareSelf k with compare k k
    compareSelf k
      | inj₁ (! ⦃ prf ⦄) with inreflex prf refl
    ... | ()
    compareSelf k
      | eq = refl
    compareSelf k
      | inj₂ (inj₂ (! ⦃ prf ⦄)) with inreflex prf refl
    ... | ()

   {- unionWith : ∀ (f : V → Maybe V → V) {l u : Ext K} {h : ℕ}
                → BOBMap (l , u) {!!}
                → BOBMap (l , u) h
                → BOBMap (l , u) {!!}
    unionWith f m n = foldr (λ (k , v) t → proj₂ $ insertWith k (f v) {{{!!}}} {{{!!}}} t) m n-}

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

    -- THIS IS MADNESS THERE HAS TO BE A BETTER WAY TO DO THIS
    BMap.lookup-insert∉ BOBMapImp k (map m) f prf =
      lookup-insert∉ k ⦃ tt ⦄ ⦃ tt ⦄ m f (toNotAny prf)
      where
        lookup-insert∉ : ∀ {l u : Ext K} {h : ℕ} → (k : K)
                         → {{l≤k : l ≺Ex # k}} {{k≤u : # k ≺Ex u}}
                         → (m : BOBMap (l , u) h)
                         → (f : Maybe V → V)
                         → k ∉ m
                         → lookup (proj₂ (insertWith k f m)) k ≡ just (f nothing)
        lookup-insert∉ {l} {u} k {{l≤k}} {{k≤u}} leaf f prf
          with insertWith {l} {u} k f {{l≤k}} {{k≤u}} leaf
        ... | _ , res with compare k k | compareSelf k
        ... | .eq | refl = refl
        lookup-insert∉ k (node p lm rm bal) f prf with compare k (proj₁ p) in comp
        lookup-insert∉ k (node p lm rm bal) f prf
          | le with lookup-insert∉ k lm f (¬Left prf)
        ... | x with insertWith k f lm
        ... | 1# , lm' with bal
        lookup-insert∉ k (node p lm rm bal) f prf
          | le | x | 1# , lm' | ~+ with compare k (proj₁ p)
        ... | le = x
        lookup-insert∉ k (node p lm rm bal) f prf
          | le | x | 1# , lm' | ~0 with compare k (proj₁ p)
        ... | le = x
        lookup-insert∉ k (node p lm rm bal) f prf
          | le | x | 1# , lm' | ~- = {!!}
        lookup-insert∉ k (node p lm rm bal) f prf
          | le | x | 0# , lm' with compare k (proj₁ p)
        ... | le = x
        lookup-insert∉ k (node p lm rm bal) f prf
          | eq with prf (here refl)
        ... | ()
        lookup-insert∉ k (node p lm rm bal) f prf
          | ge with lookup-insert∉ k rm f (¬Right prf)
        ... | x with insertWith k f rm
        ... | 1# , rm' with bal
        lookup-insert∉ k (node p lm rm bal) f prf
          | ge | x | 1# , rm' | ~+ = {!!}
        lookup-insert∉ k (node p lm rm bal) f prf
          | ge | x | 1# , rm' | ~0 with compare k (proj₁ p)
        ... | ge = x
        lookup-insert∉ k (node p lm rm bal) f prf
          | ge | x | 1# , rm' | ~- with compare k (proj₁ p)
        ... | ge = x
        lookup-insert∉ k (node p lm rm bal) f prf
          | ge | x | 0# , rm' with compare k (proj₁ p)
        ... | ge = x

    BMap.ins-comm BOBMapImp k k' f f' m notEq = {!!}

    BMap.∈-ins BOBMapImp (map m) k x f (map prf) with ∈-ins k x f {{tt}} {{tt}} m prf
      where
        ∈-ins : ∀ {l u : Ext K} {h : ℕ}
                (k x : K) (f : Maybe V → V)
                {{l≤k : l ≺Ex # k}} {{k≤u : # k ≺Ex u}}
                (m : BOBMap (l , u) h)
                → x ∈ (proj₂ $ insertWith k f m)
                → (x ≡ k) ⊎ x ∈ m
        ∈-ins {l} {u} k x f {{l≤k}} {{k≤u}} leaf prf with
          proj₂ $ insertWith {l} {u} k f {{l≤k}} {{k≤u}} leaf
        ... | node (k' , v) leaf leaf ~0 = {!!}
        ∈-ins k x f (node p lm rm bal) prf = {!!}
    ... | inj₁ e = inj₁ e
    ... | inj₂ r = inj₂ (map r)

    BMap.∪-assoc BOBMapImp = {!!}

    BMap.∪-∅ BOBMapImp (map m) f = (λ k v x → map (eqLeft k v m {!!})) , (λ k v x → {!!})
      where
        eqLeft : ∀ {l u : Ext K} {h : ℕ} (k : K) (v : V)
                 → (m : BOBMap (l , u) h)
                 → k ↦ v ∈ (foldr (λ (k , v) t → {!map $ proj₂ $ insertWith k (f v) t!}) leaf m)
                 → k ↦ v ∈ m
        eqLeft k v m prf = {!!}


    BMap.∪-∈ BOBMapImp n m f k p = {!p!}

    BMap.∪-∈' BOBMapImp n m f k (inj₁ prf) = {!!}
    BMap.∪-∈' BOBMapImp n m f k (inj₂ prf) = {!!}

    BMap.eq? BOBMapImp (map m) (map n) f with eq? m n {!!}
      where
        eq? : ∀ {l u : Ext K} {h h' : ℕ} (m : BOBMap (l , u) h) (n : BOBMap (l , u) h')
              → (∀ k v → k ↦ v ∈ m × k ↦ v ∈ n) → m ≐ n
        eq? m n f = {!!}
    ... | (prfM , prfN) =
      (λ k₁ v₁ x → map $ prfM k₁ v₁ (toAny x)) , λ k₁ v₁ x → map $ prfN k₁ v₁ (toAny x)

    BMap.eq∈ BOBMapImp = {!!}

    BMap.insert∈ BOBMapImp k v (map m) = map (insert∈ k v ⦃ tt ⦄ ⦃ tt ⦄ m)
      where
        insert∈ : ∀ {l u : Ext K} {h : ℕ} → (k : K) → (v : V)
                  {{l≤p : l ≺Ex # k}} {{p≤u : # k ≺Ex u}}
                  → (m : BOBMap (l , u) h)
                  → k ↦ v ∈ (proj₂ $ insertWith k (λ _ → v) m)
        insert∈ k v leaf = here (refl , refl)
        insert∈ k v (node p lm rm bal) with compare k (proj₁ p)
        insert∈ k v (node p lm rm bal)
          | le with insert∈ k v lm
        ... | x with insertWith k (λ _ → v) lm
        ... | 0# , _ = left x
        ... | 1# , _ with bal
        ... | ~+ = left x
        ... | ~0 = left x
        ... | ~- = {!!}
        insert∈ k v (node p lm rm bal)
          | eq = here (refl , refl)
        insert∈ k v (node p lm rm bal)
          | ge with insert∈ k v rm
        ... | x with insertWith k (λ _ → v) rm
        ... | 0# , _ = right x
        ... | 1# , _ with bal
        ... | ~+ = {!!}
        ... | ~0 = right x
        ... | ~- = right x
