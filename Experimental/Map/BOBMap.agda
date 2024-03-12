{-# OPTIONS --erasure #-}
--{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet

module Map.BOBMap {k ℓ₁} (order : OrdSet k ℓ₁) where

Order : StrictTotalOrder k k ℓ₁
Order = toStrictTotalOrder order

open import Prelude
open import Level using (Level; _⊔_; 0ℓ) renaming (suc to lsuc)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; ∣_-_∣; _≡ᵇ_; s≤s⁻¹; s<s⁻¹)
  renaming (_≤_ to _≤ℕ_; s<s to <ℕ-step; z<s to <ℕ-base; _<_ to _<ℕ_; compare to compareℕ; Ordering to Ordℕ; _⊔_ to max; s≤s to ≤ℕ-step; z≤n to ≤ℕ-base)
open import Data.Nat.Properties renaming (_≤?_ to _≤ℕ?_; _<?_ to _<ℕ?_)
open import Data.Empty renaming (⊥ to nil; ⊥-elim to nil-elim)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product
open import Data.Maybe
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Relation.Unary using (Pred)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality hiding (trans; [_])
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Nullary.Negation.Core using (¬_; contradiction)
open import Function using (_∘_; _$_; const; case_of_)
open import Relation.Binary.Definitions

open StrictTotalOrder Order renaming (Carrier to Key)
open import Data.Tree.AVL.Key Order public

private
  variable
    ℓ ℓ' ℓₚ : Level
    v : Level

ℕ₂ = Fin 2
pattern 0# = fzero
pattern 1# = fsuc fzero
pattern ## = fsuc (fsuc ())

infixl 6 _⊕_

_⊕_ : ℕ₂ → ℕ → ℕ
0# ⊕ n = n
1# ⊕ n = 1 + n

pred[_⊕_] : ℕ₂ → ℕ → ℕ
pred[ i ⊕ zero  ] = 0
pred[ i ⊕ suc n ] = i ⊕ n

infix 4 _~_⊔_

data _~_⊔_ : ℕ → ℕ → ℕ → Set where
  ~+ : ∀ {n} →     n ~ 1 + n ⊔ 1 + n
  ~0 : ∀ {n} →     n ~ n     ⊔ n
  ~- : ∀ {n} → 1 + n ~ n     ⊔ 1 + n

max~ : ∀ {i j m} → i ~ j ⊔ m → m ~ i ⊔ m
max~ ~+ = ~-
max~ ~0 = ~0
max~ ~- = ~0

~max : ∀ {i j m} → i ~ j ⊔ m → j ~ m ⊔ m
~max ~+ = ~0
~max ~0 = ~0
~max ~- = ~+

data BOBMap (V : Set v) (l u : Key⁺) : ℕ → Set (k ⊔ v ⊔ ℓ₁) where
  leaf : {{@erased l<u : l <⁺ u}} → BOBMap V l u 0
  node : ∀ {hl hr h}
         → ((k , v) : Key × V)
         → (lm : BOBMap V l [ k ] hl)
         → (rm : BOBMap V [ k ] u hr)
         → (bal : hl ~ hr ⊔ h)
         → BOBMap V l u (suc h)

module _ {v} {V : Set v} where
  rotR : ∀ {l u : Key⁺} {hr : ℕ}
         ((k , v) : Key × V)
         → BOBMap V l [ k ] (suc (suc hr))
         → BOBMap V [ k ] u hr
         → ∃ λ i → BOBMap V l u (i ⊕ (suc (suc hr)))
  rotR kv (node p lmᴸ rmᴸ ~0) rm = 1# , node p lmᴸ (node kv rmᴸ rm ~-) ~+
  rotR kv (node p lmᴸ rmᴸ ~-) rm = 0# , node p lmᴸ (node kv rmᴸ rm ~0) ~0
  rotR kv (node p lmᴸ (node pᴿ lmᴸᴿ rmᴸᴿ bal) ~+) rm =
    0# , (node pᴿ (node p lmᴸ lmᴸᴿ (max~ bal)) (node kv rmᴸᴿ rm (~max bal)) ~0)

  rotL : ∀ {l u : Key⁺} {hl : ℕ}
         ((k , v) : Key × V)
         → BOBMap V l [ k ] hl
         → BOBMap V [ k ] u (suc (suc hl))
         → ∃ λ i → BOBMap V l u (i ⊕ (suc (suc hl)))
  rotL kv lt (node p rlt rrt ~+) = 0# , (node p (node kv lt rlt ~0) rrt ~0)
  rotL kv lt (node p rlt rrt ~0) = 1# , (node p (node kv lt rlt ~+) rrt ~-)
  rotL kv lt (node p (node p' rllt rlrt bal) rrt ~-) =
    0# , (node p' (node kv lt rllt (max~ bal)) (node p rlrt rrt (~max bal)) ~0)

  joinˡ⁺ : ∀ {l u : Key⁺} {h} {hl} {hr}
    → (p : Key × V)
    → ∃ (λ i → BOBMap V l [ proj₁ p ] (i ⊕ hl))
    → BOBMap V [ proj₁ p ] u hr
    → hl ~ hr ⊔ h
    → ∃ (λ i → BOBMap V l u (i ⊕ suc h))
  joinˡ⁺ p (0# , lt) rt bal = 0# , node p lt rt bal
  joinˡ⁺ p (1# , lt) rt ~+  = 0# , node p lt rt ~0
  joinˡ⁺ p (1# , lt) rt ~0  = 1# , node p lt rt ~-
  joinˡ⁺ p (1# , lt) rt ~-  = rotR p lt rt

  joinʳ⁺ : ∀ {l u : Key⁺} {h} {hl} {hr}
    → (p : Key × V)
    → BOBMap V l [ proj₁ p ] hl
    → ∃ (λ i → BOBMap V [ proj₁ p ] u (i ⊕ hr))
    → hl ~ hr ⊔ h
    → ∃ (λ i → BOBMap V l u (i ⊕ suc h))
  joinʳ⁺ p lt (0# , rt) bal = 0# , node p lt rt bal
  joinʳ⁺ p lt (1# , rt) ~+ = rotL p lt rt
  joinʳ⁺ p lt (1# , rt) ~0 = 1# , node p lt rt ~+
  joinʳ⁺ p lt (1# , rt) ~- = 0# , node p lt rt ~0

  insertWith : {l u : Key⁺} {h : ℕ} (k : Key) (f : Maybe V → V)
               {{@erased l≤p : l <⁺ [ k ]}} {{@erased p≤u : [ k ] <⁺ u}}
               → BOBMap V l u h
               → ∃ λ i → BOBMap V l u (i ⊕ h)
  insertWith k f leaf = 1# , node (k , f nothing) leaf leaf ~0
  insertWith k f (node p lt rt bal) with compare k (proj₁ p)
  ... | tri< k<p _ _ = joinˡ⁺ p (insertWith k f {{p≤u = [ k<p ]ᴿ}} lt) rt bal
  ... | tri≈ _ refl _ = 0# , node (k , f (just (proj₂ p))) lt rt bal
  ... | tri> _ _ p<k = joinʳ⁺ p lt (insertWith k f {{[ p<k ]ᴿ}} rt) bal

  insert : {l u : Key⁺} {h : ℕ} (kv : Key × V)
           {{@erased l≤p : l <⁺ [ (proj₁ kv) ]}}
           {{@erased p≤u : [ (proj₁ kv) ] <⁺ u}}
           → BOBMap V l u h
           → ∃ λ i → BOBMap V l u (i ⊕ h)
  insert (k , v) m = insertWith k (λ _ → v) m

  lookup : ∀ {l u : Key⁺} {h : ℕ}
           → BOBMap V l u h
           → Key
           → Maybe V
  lookup leaf k = nothing
  lookup (node p lt rt bal) k with compare k (proj₁ p)
  ... | tri< k<p _ _ = lookup lt k
  ... | tri≈ _ refl _ = just (proj₂ p)
  ... | tri> _ _ p<k = lookup rt k

  record Cons (p : Key × V) (l u : Key⁺) (h : ℕ) : Set (k ⊔ v ⊔ ℓ₁) where
    constructor cons
    field
      head : Key × V
      @erased l<u : l <⁺ [ proj₁ head ]
      tail : ∃ λ i → BOBMap V [ proj₁ head ] u (i ⊕ h)

  uncons : ∀ {l u h h1 h2}
           → ((k , v) : Key × V)
           → h1 ~ h2 ⊔ h
           → BOBMap V l [ k ] h1
           → BOBMap V [ k ] u h2
           → Cons (k , v) l u h
  uncons p b (leaf {{l<u}}) r = cons p l<u (case b of
    λ { ~+ → 0# , r
      ; ~0 → 0# , r })
  uncons p b (node p' l c bl) r with uncons p' bl l c
  ... | cons head l<u tail = cons head l<u (case tail of
    λ { (1# , t) → 1# , node p t r b
      ; (0# , t) → case b of
        λ { ~- → 0# , node p t r ~0
          ; ~0 → 1# , node p t r ~+
          ; ~+ → rotL p t r } })

  reduce : ∀ {l y u h}
          → {{@erased l≤y : l <⁺ y}}
          → BOBMap V y u h
          → BOBMap V l u h
  reduce {l} {y} {u} {{a}} (leaf {{b}}) = leaf {{trans⁺ l a b}}
  reduce {{a}} (node p l r bal) = node p (reduce {{a}} l) r bal

  raise : ∀ {l y u h}
          → {{@erased y≤u : y <⁺ u}}
          → BOBMap V l y h
          → BOBMap V l u h
  raise {x} {y} {z} {{a}} (leaf {{b}}) = leaf {{trans⁺ x b a}}
  raise {{a}} (node p l r bal) = node p l (raise {{a}} r) bal

  join : {l u : Key⁺} {k : Key} {hl hr h : ℕ}
         → BOBMap V [ k ] u hr
         → hl ~ hr ⊔ h
         → BOBMap V l [ k ] hl
         → ∃ λ i → BOBMap V l u (i ⊕ h)
  join leaf ~- lt = 0# , (raise lt)
  join {l} {u} {k} (leaf {{k<u}}) ~0 (leaf {{l<k}}) =
    0# , (leaf {{trans⁺ l l<k k<u}})
  join (node p rlt rrt br) b tl with uncons p br rlt rrt
  ... | cons head l<u (1# , tr') = 1# , node head (raise {{l<u}} tl) tr' b
  ... | cons head l<u (0# , tr') with b
  ... | ~- = rotR head (raise {{l<u}} tl) tr'
  ... | ~0 = 1# , node head (raise {{l<u}} tl) tr' ~-
  ... | ~+ = 0# , node head (raise {{l<u}} tl) tr' ~0

-- * UNION STARTS HERE -----------------------------------------------------

  @erased mklim : ∀ {l u h}
          → BOBMap V l u h
          → l <⁺ u
  mklim (leaf {{p}}) = p
  mklim {l} {u} (node p lt rt bal) = trans⁺ l (mklim lt) (mklim rt)

  lemR : {n m : ℕ} → max (suc (m + n)) m ≡ suc (m + n)
  lemR {n} {zero} = refl
  lemR {n} {suc m} rewrite lemR {n} {m} = refl

  lemRR : {n m : ℕ} → max (suc (suc (m + n))) m ≡ suc (suc (m + n))
  lemRR {n} {zero} = refl
  lemRR {n} {suc m} rewrite lemRR {n} {m} = refl

  lemL : {n m : ℕ} → max m (suc (m + n)) ≡ suc (m + n)
  lemL {n} {zero} = refl
  lemL {n} {suc m} rewrite lemL {n} {m} = refl

  lemLL : {n m : ℕ} → max m (suc (suc (m + n))) ≡ suc (suc (m + n))
  lemLL {n} {zero} = refl
  lemLL {n} {suc m} rewrite lemLL {n} {m} = refl

  lemC : {m : ℕ} → max m m ≡ m
  lemC {zero} = refl
  lemC {suc m} rewrite lemC {m} = refl

  lem4L : ∀ {a} → max (suc a) a ≡ suc a
  lem4L {zero} = refl
  lem4L {suc a} rewrite lem4L {a} = refl

  lem4R : ∀ {a} → max a (suc a) ≡ suc a
  lem4R {zero} = refl
  lem4R {suc a} rewrite lem4R {a} = refl

  data Balancing : Rel ℕ 0ℓ where
    left : ∀ hr k → Balancing (suc (suc (hr + k))) hr
    1-offL : ∀ h → Balancing (suc h) h
    balanced : ∀ h → Balancing h h
    1-offR : ∀ h → Balancing h (suc h)
    right : ∀ hl k → Balancing hl (suc (suc (hl + k)))

  compareBalance : ∀ hl hr → Balancing hl hr
  compareBalance zero zero = balanced zero
  compareBalance zero (suc zero) = 1-offR zero
  compareBalance zero (suc (suc b)) = right zero b
  compareBalance (suc zero) zero = 1-offL zero
  compareBalance (suc (suc a)) zero = left zero a
  {-# CATCHALL #-}
  compareBalance (suc a) (suc b) with compareBalance a b
  ... | left .b k = left (suc b) k
  ... | 1-offL .b = 1-offL (suc b)
  ... | balanced .a = balanced (suc a)
  ... | 1-offR .a = 1-offR (suc a)
  ... | right .a k = right (suc a) k

  postulate
    illegal~⊔2L : ∀ {a b c} → a ~ b ⊔ suc (suc a + c) → nil
    illegal~⊔2R : ∀ {a b c} → a ~ b ⊔ suc (suc b + c) → nil
    illegal~⊔3L : ∀ {a b c d} → a ~ b ⊔ suc (suc (suc a + c + d)) → nil
    illegal~⊔3R : ∀ {a b c d} → a ~ b ⊔ suc (suc (suc b + c + d)) → nil

  gJoinRight : {hr x : ℕ} {l u : Key⁺}
                → ((k , v) : Key × V)
                → BOBMap V l [ k ] (suc (suc (hr + x)))
                → BOBMap V [ k ] u hr
                → ∃ λ i → BOBMap V l u (i ⊕ suc (suc (hr + x)))
  gJoinRight {hr} {x} {ₗ} {ᵘ} p (node {hl = hl} {hr = hc} p2 l c b) r
    with compareBalance hc hr
  ... | left .hr k = joinʳ⁺ p2 l T' b
    where
      T' : ∃ λ i → BOBMap V [ proj₁ p2 ] ᵘ (i ⊕ hc)
      T' = gJoinRight p c r

  ... | 1-offL .hr = joinʳ⁺ p2 l T' b
    where
      T' : ∃ λ i → BOBMap V [ proj₁ p2 ] ᵘ (i ⊕ hc)
      T' = 1# , node p c r ~-

  ... | balanced .hr = joinʳ⁺ p2 l T' b
    where
      T' : ∃ λ i → BOBMap V [ proj₁ p2 ] ᵘ (i ⊕ hc)
      T' = 1# , node p c r ~0

  ... | right .hc k = nil-elim (illegal~⊔3R b )
  ... | 1-offR .hc = nil-elim (illegal~⊔2R b)

  gJoinLeft : {hl x : ℕ} {l u : Key⁺}
               → ((k , v) : Key × V)
               → BOBMap V l [ k ] hl
               → BOBMap V [ k ] u (suc (suc (hl + x)))
               → ∃ λ i → BOBMap V l u (i ⊕ suc (suc (hl + x)))
  gJoinLeft {hl} {x} {ₗ} {ᵘ} p l (node {hl = hc} {hr = hr} p2 c r b)
    with compareBalance hc hl
  ... | left     .hl k = joinˡ⁺ p2 T' r b
    where
      T' : ∃ λ i → BOBMap V ₗ [ proj₁ p2 ] (i ⊕ hc)
      T' = gJoinLeft p l c

  ... | 1-offL   .hl   = joinˡ⁺ p2 T' r b
    where
      T' : ∃ λ i → BOBMap V ₗ [ proj₁ p2 ] (i ⊕ hc)
      T' = 1# , node p l c ~+

  ... | balanced .hl   = joinˡ⁺ p2 T' r b
    where
      T' : ∃ λ i → BOBMap V ₗ [ proj₁ p2 ] (i ⊕ hc)
      T' = _ , node p l c ~0

  ... | 1-offR .hc = nil-elim (illegal~⊔2L b)
  ... | right .hc k = nil-elim (illegal~⊔3L b)

  gJoin : {hl hr : ℕ} {l u : Key⁺}
          → ((k , v) : Key × V)
          → BOBMap V l [ k ] hl
          → BOBMap V [ k ] u hr
          → ∃ λ i → BOBMap V l u (i ⊕ max hl hr)
  gJoin {hl} {hr} p l r
    with compareBalance hl hr
  ... | left     .hr k rewrite lemRR {k} {hr} = gJoinRight p l r
  ... | 1-offL   .hr   rewrite lem4L {hr} = 1# , node p l r ~-
  ... | balanced .hl   rewrite lemC {hl}  = 1# , node p l r ~0
  ... | 1-offR   .hl   rewrite lem4R {hl} = 1# , node p l r ~+
  ... | right    .hl k rewrite lemLL {k} {hl} = gJoinLeft p l r

  splitLT : ∀ {l u h}
            → ((k , v) : Key × V)
            → {{@erased l≤k : l <⁺ [ k ]}}
            → BOBMap V l u h
            → ∃ λ n → BOBMap V l [ k ] n
  splitLT x (leaf {{l<u}}) = 0 , leaf
  splitLT (k , v) (node (k' , v') lt rt bal) with compare k k'
  ... | tri< k<p _ _ = splitLT (k , v) lt
  ... | tri≈ _ refl _ = _ , lt
  ... | tri> _ _ p<k = let (n , m) = splitLT (k , v) {{[ p<k ]ᴿ}} rt
                           (i , t) = gJoin (k' , v') lt m
                       in _ , t

  splitGT : ∀ {l u h}
            → ((k , v) : Key × V)
            → {{@erased l≤u : [ k ] <⁺ u}}
            → BOBMap V l u h
            → ∃ λ n → BOBMap V [ k ] u n
  splitGT x (leaf {{l<u}})= 0 , leaf
  splitGT (k , v) (node (k' , v') lt rt bal) with compare k k'
  ... | tri≈ _ refl _ = _ , rt
  ... | tri> _ _ p<k = splitGT (k , v) rt
  ... | tri< k<p _ _ = let (n , m) = splitGT (k , v) {{[ k<p ]ᴿ}} lt
                           (i , t) = gJoin (k' , v') m rt
                       in _ , t

  unionWith : {h1 h2 : ℕ} → ∀ {l u}
              → (V → Maybe V → V)
              → BOBMap V l u h1
              → BOBMap V l u h2
              → ∃ λ n → BOBMap V l u (n ⊕ max h1 h2)
  unionWith {h1} {h2} f n m with compareℕ h1 h2
  ... | Ordℕ.less    .h1 k rewrite lemL {k} {h1} = {!!}
  ... | Ordℕ.equal   .h1   rewrite lemC {h1}     = {!!}
  ... | Ordℕ.greater .h2 k rewrite lemR {k} {h2} = unionRight f m n
    where
      -- express h2 in terms of h1 (see above)
      unionRight : {h1 h2 : ℕ} → {l u : Key⁺}
               → (V → Maybe V → V)
               → BOBMap V l u h1
               → BOBMap V l u h2
                → ∃ λ i → BOBMap V l u (i ⊕ h2)
      unionRight f leaf (leaf {{prf}}) = 0# , leaf {{prf}}
      unionRight f leaf (node p l r b) = 0# , (node p l r b)
      unionRight f (node p l r b) m with (splitLT p {{mklim l}} m) , (splitGT p {{mklim r}} m)
      ... | (hl1 , l1) , (hr1 , r1) with unionWith f l1 l
      ... | hl2 , l2 with unionWith f r1 r
      ... | hr2 , r2 = {!l2 , r2!}

  -- * DELETE STARTS HERE ----------------------------------------------------

  joinˡ⁻ : ∀ {l u} {hl hr h}
          → ((k , v) : Key × V)
          → ∃ (λ i → BOBMap V l [ k ] pred[ i ⊕ hl ])
          → BOBMap V [ k ] u hr
          → hl ~ hr ⊔ h
          → ∃ λ i → BOBMap V l u (i ⊕ h)
  joinˡ⁻ {hl = zero} kv (0# , lt) rt b = 1# , node kv lt rt b
  joinˡ⁻ {hl = zero} kv (1# , lt) rt b = 1# , node kv lt rt b
  joinˡ⁻ {hl = suc hl} kv (0# , lt) rt ~+ = rotL kv lt rt
  joinˡ⁻ {hl = suc hl} kv (0# , lt) rt ~0 = 1# , (node kv lt rt ~+)
  joinˡ⁻ {hl = suc hl} kv (0# , lt) rt ~- = 0# , (node kv lt rt ~0)
  joinˡ⁻ {hl = suc hl} kv (1# , lt) rt b = 1# , (node kv lt rt b)

  joinʳ⁻ : ∀ {l u} {hl hr h}
           → ((k , v) : Key × V)
           → BOBMap V l [ k ] hl
           → ∃ (λ i → BOBMap V [ k ] u pred[ i ⊕ hr ])
           → hl ~ hr ⊔ h
           → ∃ λ i → BOBMap V l u (i ⊕ h)
  joinʳ⁻ {hr = zero} kv lt (0# , rt) b = 1# , node kv lt rt b
  joinʳ⁻ {hr = zero} kv lt (1# , rt) b = 1# , node kv lt rt b
  joinʳ⁻ {hr = suc hr} kv lt (0# , rt) ~+ = 0# , node kv lt rt ~0
  joinʳ⁻ {hr = suc hr} kv lt (0# , rt) ~0 = 1# , node kv lt rt ~-
  joinʳ⁻ {hr = suc hr} kv lt (0# , rt) ~- = rotR kv lt rt
  joinʳ⁻ {hr = suc hr} kv lt (1# , rt) b = 1# , node kv lt rt b

  delete : ∀ {l u : Key⁺} {h : ℕ} (k : Key)
           {{l≤p : l <⁺ [ k ]}} {{p≤u : [ k ] <⁺ u}}
           → BOBMap V l u h
           → ∃ λ i → BOBMap V l u pred[ i ⊕ h ]
  delete k leaf = 0# , leaf
  delete k (node p lt rt bal) with compare k (proj₁ p)
  ... | tri< k<p _ _ = joinˡ⁻ p (delete k {{p≤u = [ k<p ]ᴿ}} lt) rt bal
  ... | tri≈ _ refl _ = join rt bal lt
  ... | tri> _ _ p<k = joinʳ⁻ p lt (delete k {{[ p<k ]ᴿ}} rt) bal

  -- * DELETE ENDS HERE ------------------------------------------------

  data Any (P : Pred V ℓₚ) {l u : Key⁺} (kₚ : Key) :
    ∀ {h : ℕ} → BOBMap V l u h → Set (k ⊔ ℓ₁ ⊔ v ⊔ ℓₚ) where
    here : ∀ {h hl hr} {v : V}
           {{@erased l≤k : l <⁺ [ kₚ ]}} {{@erased k≤u : [ kₚ ] <⁺ u}}
           → P v
           → {lm : BOBMap V l [ kₚ ] hl}
           {rm : BOBMap V [ kₚ ] u hr}
           {bal : hl ~ hr ⊔ h}
           → Any P kₚ (node (kₚ , v) lm rm bal)

    left : ∀ {h hl hr} {(k' , v) : Key × V}
           {lm : BOBMap V l [ k' ] hl}
           {{k≺k' : [ kₚ ] <⁺ [ k' ]}}
           → Any P kₚ lm
           → {rm : BOBMap V [ k' ] u hr}
           {bal : hl ~ hr ⊔ h}
           → Any P kₚ (node (k' , v) lm rm bal)

    right : ∀ {h hl hr} {(k' , v) : Key × V}
           {lm : BOBMap V l [ k' ] hl}
           {rm : BOBMap V [ k' ] u hr}
           {{k'≤k : [ k' ] <⁺ [ kₚ ]}}
           → Any P kₚ rm
           → {bal : hl ~ hr ⊔ h}
           → Any P kₚ (node (k' , v) lm rm bal)

  foldr : ∀ {l u} {h : ℕ} {n : Level} {A : Set n}
          → (Key × V → A → A)
          → A
          → BOBMap V l u h
          → A
  foldr f g leaf = g
  foldr f g (node p l r bal) = foldr f (f p (foldr f g r)) l

{-

  ratio : ℕ
  ratio = 5 -- source?

  data CmpResult : Set where
    LT : CmpResult
    EQ : CmpResult
    GT : CmpResult

  cmp : ℕ → ℕ → CmpResult
  cmp zero    zero    = EQ
  cmp zero    _       = LT
  cmp _       zero    = GT
  cmp (suc n) (suc m) = cmp n m

  link : ∀ {h1 h2}
         → (k : K)
         → ∀ {l u x y}
         → {{l≤p : l ≺Ex  (# k)}} → {{p≤u :(# k) ≺Ex u}}
         → (Maybe V → V)
         → {{l≤y : l ≺Ex y}} → {{x≤u : x ≺Ex u}}
         → BOBMap (l , x) h1
         → BOBMap (y , u) h2
         → ∃ λ n → BOBMap (l , u) n
  link {h1} {h2} k {l} {u} {x} {y} {{p4}} {{p5}} f {{p1}} {{p2}} (leaf {{p3}}) m
    with insertWith {l} {u} k f {{p4}} {{p5}} (reduce p1 m)
  ... | fst , snd = (fst ⊕ h2) , snd
  link {h1} {h2} k {l} {u} {x} {y} {{p4}} {{p5}} f {{p1}} {{p2}} n (leaf {{p3}})
    with insertWith {l} {u} k f {{p4}} {{p5}} (raise p2 n)
  ... | fst , snd = (fst ⊕ h1) , snd
  link {h1} {h2} k f n@(node (k1 , _) l1 r1 bal1) m@(node (k2 , _) l2 r2 bal2)
    with cmp (ratio * h1) h2
  ... | LT = let (i1 , t1) = link k f n {!!}
             in {!!}
  ... | EQ = {!!}
  ... | GT = {!!}

-}
-- -}
-- -}
-- -}
-- -}
-- -}
