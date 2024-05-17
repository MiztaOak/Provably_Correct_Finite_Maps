{-# OPTIONS --erasure #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import OrdSet

module Map.BOBMap {k ℓ₁} (order : OrdSet k ℓ₁) where

Order : StrictTotalOrder k k ℓ₁
Order = toStrictTotalOrder order

open import Prelude
open import Level using (Level; _⊔_; 0ℓ) renaming (suc to lsuc)
open import Data.Nat.Base
  using (ℕ; zero; suc; pred; _+_; _*_; _<_; _≤_; z<s; s<s; z≤n; s≤s; s≤s⁻¹)
  renaming (_⊔_ to max; compare to compareℕ; Ordering to Ordℕ)
open import Data.Nat.Properties
  using (n<1+n; n≤1+n; ≤-refl; <⇒≤; m≤n⇒m≤1+n; ≤-trans; +-identityʳ; m≤n⇒m⊔n≡n; ⊔-comm; _≤?_; n≤0⇒n≡0; suc-injective; ≤-reflexive; ⊔-assoc; ⊔-idem; ⊔-sel; ⊔-lub; m≤n⇒m≤n⊔o; m≤n⇒m≤o⊔n)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product
open import Data.Sum using (_⊎_) renaming (inj₁ to inl; inj₂ to inr)
open import Data.Maybe
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.Core using (Rel)
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality hiding (trans; [_])
open import Function using (_∘_; _$_; const; case_of_)
open import Relation.Binary.Definitions
open import Relation.Nullary using (¬_; contradiction)
open import Relation.Nullary.Decidable using (yes; no)

open import Map.UnionLemmas

open StrictTotalOrder Order using (compare) renaming (Carrier to Key)
open import Data.Tree.AVL.Key Order public

private
  variable
    ℓ ℓ' ℓₚ ℓₐ : Level
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

data BOBMap (@0 V : Set v) (@0 l u : Key⁺) : @0 ℕ → Set (k ⊔ v ⊔ ℓ₁) where
  leaf : {{@erased l<u : l <⁺ u}} → BOBMap V l u 0
  node : ∀ {hl hr h}
         → ((k , v) : Key × V)
         → (lm : BOBMap V l [ k ] hl)
         → (rm : BOBMap V [ k ] u hr)
         → (bal : hl ~ hr ⊔ h)
         → BOBMap V l u (suc h)

module _ {v} {V : Set v} where
  singleton : ∀ {@0 l u : Key⁺} (k : Key) → V
    → ⦃ l<k : l <⁺ [ k ] ⦄ ⦃ k<u : [ k ] <⁺ u ⦄
    → BOBMap V l u 1
  singleton k v = node (k , v) leaf leaf ~0

  data Any (P : Pred V ℓₚ) {@0 l u : Key⁺} (kₚ : Key) :
    ∀ {@0 h : ℕ} → @erased BOBMap V l u h → Set (k ⊔ ℓ₁ ⊔ v ⊔ ℓₚ) where
    here : ∀ {@0 h hl hr} {@0 v : V}
           {{@erased l≤k : l <⁺ [ kₚ ]}} {{@erased k≤u : [ kₚ ] <⁺ u}}
           → P v
           → {@erased lm : BOBMap V l [ kₚ ] hl}
           {@erased rm : BOBMap V [ kₚ ] u hr}
           {@erased bal : hl ~ hr ⊔ h}
           → Any P kₚ (node (kₚ , v) lm rm bal)

    left : ∀ {@0 h hl hr} {(k' , v) : Key × V}
           {@erased lm : BOBMap V l [ k' ] hl}
           {{@erased k≺k' : [ kₚ ] <⁺ [ k' ]}}
           → Any P kₚ lm
           → {@erased rm : BOBMap V [ k' ] u hr}
           {@erased bal : hl ~ hr ⊔ h}
           → Any P kₚ (node (k' , v) lm rm bal)

    right : ∀ {@0 h hl hr} {(k' , v) : Key × V}
           {@erased lm : BOBMap V l [ k' ] hl}
           {@erased rm : BOBMap V [ k' ] u hr}
           {{@erased k'≤k : [ k' ] <⁺ [ kₚ ]}}
           → Any P kₚ rm
           → {@erased bal : hl ~ hr ⊔ h}
           → Any P kₚ (node (k' , v) lm rm bal)

  fldr : ∀ {@0 l u} {h : ℕ} {n : Level} {A : Set n}
          → (Key × V → A → A)
          → A
          → BOBMap V l u h
          → A
  fldr f g leaf = g
  fldr f g (node p l r bal) = fldr f (f p (fldr f g r)) l

  record Cons (@0 l u : Key⁺) (h : ℕ) : Set (k ⊔ v ⊔ ℓ₁) where
    constructor cons
    field
      head : Key × V
      @erased l<u : l <⁺ [ proj₁ head ]
      tail : ∃ λ i → BOBMap V [ proj₁ head ] u (i ⊕ h)

  reduce : ∀ {@0 l y u h}
          → {{@erased l≤y : l <⁺ y}}
          → BOBMap V y u h
          → BOBMap V l u h
  reduce {l} {y} {u} {{a}} (leaf {{b}}) = leaf {{trans⁺ l a b}}
  reduce {{a}} (node p l r bal) = node p (reduce {{a}} l) r bal

  raise : ∀ {@0 l y u h}
          → {{@erased y≤u : y <⁺ u}}
          → BOBMap V l y h
          → BOBMap V l u h
  raise {x} {y} {z} {{a}} (leaf {{b}}) = leaf {{trans⁺ x b a}}
  raise {{a}} (node p l r bal) = node p l (raise {{a}} r) bal

  @erased mklim : ∀ {l u h}
          → BOBMap V l u h
          → l <⁺ u
  mklim (leaf {{p}}) = p
  mklim {l} {u} (node p lt rt bal) = trans⁺ l (mklim lt) (mklim rt)
  private
    _∈_ : Key → {@0 l u : Key⁺} {h : ℕ} → BOBMap V l u h → Set (k ⊔ ℓ₁ ⊔ v)
    k ∈ m = Any {ℓₚ = 0ℓ} (λ _ → True) k m

  _∈?_ : ∀ {@0 l u h} (x : Key)
         → (a : BOBMap V l u h)
         → Maybe (x ∈ a)
  _∈?_ x leaf = nothing
  _∈?_ x (node p lt rt bal) with compare x (proj₁ p)
  ... | tri< prf _ _ = _∈?_ x lt >>= λ α → just (left {{[ prf ]ᴿ}} α)
  ... | tri≈ _ refl _ = just $ here {{mklim lt}} {{mklim rt}} tt
  ... | tri> _ _ prf = (_∈?_ x rt) >>= λ α → just (right {{[ prf ]ᴿ}} α)

-- * JOINS STARTS HERE -----------------------------------------------------
  joinˡ⁺ : ∀ {@0 l u : Key⁺} {h hl hr}
    → (p : Key × V)
    → ∃ (λ i → BOBMap V l [ proj₁ p ] (i ⊕ hl))
    → BOBMap V [ proj₁ p ] u hr
    → hl ~ hr ⊔ h
    → ∃ (λ i → BOBMap V l u (i ⊕ suc h))
  joinˡ⁺ p (0# , lt) rt bal = 0# , node p lt rt bal
  joinˡ⁺ p (1# , lt) rt ~+  = 0# , node p lt rt ~0
  joinˡ⁺ p (1# , lt) rt ~0  = 1# , node p lt rt ~-
  joinˡ⁺ p (1# , node pᴸ ltᴸ rtᴸ ~0) rt ~- = 1# , node pᴸ ltᴸ (node p rtᴸ rt ~-) ~+
  joinˡ⁺ p (1# , node pᴸ ltᴸ rtᴸ ~-) rt ~- = 0# , (node pᴸ ltᴸ (node p rtᴸ rt ~0) ~0)
  joinˡ⁺ p (1# , node pᴸ ltᴸ (node pᴿ ltᴿ rtᴿ b) ~+) rt ~- =
    0# , (node pᴿ (node pᴸ ltᴸ ltᴿ (max~ b)) (node p rtᴿ rt (~max b)) ~0)

  joinʳ⁺ : ∀ {@0 l u : Key⁺} {h hl hr}
    → (p : Key × V)
    → BOBMap V l [ proj₁ p ] hl
    → ∃ (λ i → BOBMap V [ proj₁ p ] u (i ⊕ hr))
    → hl ~ hr ⊔ h
    → ∃ (λ i → BOBMap V l u (i ⊕ suc h))
  joinʳ⁺ p lt (0# , rt) bal = 0# , node p lt rt bal
  joinʳ⁺ p lt (1# , rt) ~0 = 1# , node p lt rt ~+
  joinʳ⁺ p lt (1# , rt) ~- = 0# , node p lt rt ~0
  joinʳ⁺ p lt (1# , node pᴿ ltᴿ rtᴿ ~+) ~+ = 0# , (node pᴿ (node p lt ltᴿ ~0) rtᴿ ~0)
  joinʳ⁺ p lt (1# , node pᴿ ltᴿ rtᴿ ~0) ~+ = 1# , node pᴿ (node p lt ltᴿ ~+) rtᴿ ~-
  joinʳ⁺ p lt (1# , node pᴿ (node pᴸ ltᴸ rtᴸ b) rtᴿ ~-) ~+ =
    0# , node pᴸ (node p lt ltᴸ (max~ b)) (node pᴿ rtᴸ rtᴿ (~max b)) ~0

  joinˡ⁻ : ∀ {@0 l u} {hl hr h}
          → ((k , v) : Key × V)
          → ∃ (λ i → BOBMap V l [ k ] pred[ i ⊕ hl ])
          → BOBMap V [ k ] u hr
          → hl ~ hr ⊔ h
          → ∃ λ i → BOBMap V l u (i ⊕ h)
  joinˡ⁻ {hl = zero} kv (0# , lt) rt b = 1# , node kv lt rt b
  joinˡ⁻ {hl = zero} kv (1# , lt) rt b = 1# , node kv lt rt b
  joinˡ⁻ {hl = suc hl} kv (0# , lt) rt ~+ = joinʳ⁺ kv lt (1# , rt) ~+
  joinˡ⁻ {hl = suc hl} kv (0# , lt) rt ~0 = 1# , (node kv lt rt ~+)
  joinˡ⁻ {hl = suc hl} kv (0# , lt) rt ~- = 0# , (node kv lt rt ~0)
  joinˡ⁻ {hl = suc hl} kv (1# , lt) rt b = 1# , (node kv lt rt b)

  joinʳ⁻ : ∀ {@0 l u} {hl hr h}
           → ((k , v) : Key × V)
           → BOBMap V l [ k ] hl
           → ∃ (λ i → BOBMap V [ k ] u pred[ i ⊕ hr ])
           → hl ~ hr ⊔ h
           → ∃ λ i → BOBMap V l u (i ⊕ h)
  joinʳ⁻ {hr = zero} kv lt (0# , rt) b = 1# , node kv lt rt b
  joinʳ⁻ {hr = zero} kv lt (1# , rt) b = 1# , node kv lt rt b
  joinʳ⁻ {hr = suc hr} kv lt (0# , rt) ~+ = 0# , node kv lt rt ~0
  joinʳ⁻ {hr = suc hr} kv lt (0# , rt) ~0 = 1# , node kv lt rt ~-
  joinʳ⁻ {hr = suc hr} kv lt (0# , rt) ~- = joinˡ⁺ kv (1# , lt) rt ~-
  joinʳ⁻ {hr = suc hr} kv lt (1# , rt) b = 1# , node kv lt rt b

  uncons : ∀ {@0 l u h}
             → BOBMap V l u (suc h)
             → Cons l u h
  uncons (node p leaf rm ~+) = cons p (mklim leaf) (0# , rm)
  uncons (node p leaf rm ~0) = cons p (mklim leaf) (0# , rm)
  {-# CATCHALL #-}
  uncons (node {suc _} p lm rm bal) with uncons lm
  ... | cons head l<u tail = cons head l<u (joinˡ⁻ p tail rm bal)

  join : {@0 l u : Key⁺} {k : Key} {hl hr h : ℕ}
         → BOBMap V l [ k ] hl
         → BOBMap V [ k ] u hr
         → hl ~ hr ⊔ h
         → ∃ λ i → BOBMap V l u (i ⊕ h)
  join lt leaf ~0 = 0# , raise lt
  join lt leaf ~- = 0# , raise lt
  join lt rt@(node _ _ _ _) b with uncons rt
  ... | cons head l<u tail = joinʳ⁻ head (raise ⦃ l<u ⦄ lt) tail b

  insertWith : {@0 l u : Key⁺} {@0 h : ℕ} (k : Key) (f : Maybe V → V)
               {{@erased l≤u : l <⁺ [ k ]}} {{@erased p≤u : [ k ] <⁺ u}}
               → BOBMap V l u h
               → ∃ λ i → BOBMap V l u (i ⊕ h)
  insertWith k f leaf = 1# , node (k , f nothing) leaf leaf ~0
  insertWith k f (node p lt rt bal) with compare k (proj₁ p)
  ... | tri< k<p _ _ = joinˡ⁺ p (insertWith k f {{p≤u = [ k<p ]ᴿ}} lt) rt bal
  ... | tri≈ _ refl _ = 0# , node (k , f (just (proj₂ p))) lt rt bal
  ... | tri> _ _ p<k = joinʳ⁺ p lt (insertWith k f {{[ p<k ]ᴿ}} rt) bal

  insert : {@0 l u : Key⁺} {@0 h : ℕ} (kv : Key × V)
           {{@erased l≤p : l <⁺ [ (proj₁ kv) ]}}
           {{@erased p≤u : [ (proj₁ kv) ] <⁺ u}}
           → BOBMap V l u h
           → ∃ λ i → BOBMap V l u (i ⊕ h)
  insert (k , v) m = insertWith k (λ _ → v) m

  lookup : ∀ {@0 l u : Key⁺} {@0 h : ℕ}
           → BOBMap V l u h
           → Key
           → Maybe V
  lookup leaf k = nothing
  lookup (node p lt rt bal) k with compare k (proj₁ p)
  ... | tri< k<p _ _ = lookup lt k
  ... | tri≈ _ refl _ = just (proj₂ p)
  ... | tri> _ _ p<k = lookup rt k

  -- * GENERAL JOIN STARTS HERE ----------------------------------------------

  -- TODO: Look over these lemmas
  lemR : {n m : ℕ} → max (suc (m + n)) m ≡ suc (m + n)
  lemR {n} {zero} = refl
  lemR {n} {suc m} rewrite lemR {n} {m} = refl

  lemRR+n : {n m : ℕ} → max (suc (suc (m + n))) m ≡ suc (suc (m + n))
  lemRR+n {n} {zero} = refl
  lemRR+n {n} {suc m} rewrite lemRR+n {n} {m} = refl

  lemRR : {m : ℕ} → max (suc (suc m)) m ≡ suc (suc m)
  lemRR {zero} = refl
  lemRR {suc m} rewrite lemRR {m} = refl

  lemL : {n m : ℕ} → max m (suc (m + n)) ≡ suc (m + n)
  lemL {n} {zero} = refl
  lemL {n} {suc m} rewrite lemL {n} {m} = refl

  lemLL+n : {n m : ℕ} → max m (suc (suc (m + n))) ≡ suc (suc (m + n))
  lemLL+n {n} {zero} = refl
  lemLL+n {n} {suc m} rewrite lemLL+n {n} {m} = refl

  lemC : {m : ℕ} → max m m ≡ m
  lemC {zero} = refl
  lemC {suc m} rewrite lemC {m} = refl

  lem4L : ∀ {a} → max (suc a) a ≡ suc a
  lem4L {zero} = refl
  lem4L {suc a} rewrite lem4L {a} = refl

  lem4Ln : ∀ {a n} → max (suc (a + n)) (a + n) ≡ suc (a + n)
  lem4Ln {zero} {n} rewrite lem4L {n} = refl
  lem4Ln {suc a} {n} rewrite lem4Ln {a} {n} = refl

  lem4R : ∀ {a} → max a (suc a) ≡ suc a
  lem4R {zero} = refl
  lem4R {suc a} rewrite lem4R {a} = refl
  -- END OF TODO

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

  -- these are highlighted yellow, why?
  illegal~⊔2L : ∀ {a b c} → a ~ b ⊔ suc (suc a + c) → ⊥
  illegal~⊔2L {a} {b} {c} = λ ()

  illegal~⊔2R : ∀ {a b c} → a ~ b ⊔ suc (suc b + c) → ⊥
  illegal~⊔2R {a} {b} {c} = λ ()

  illegal~⊔3L : ∀ {a b c d} → a ~ b ⊔ suc (suc (suc a + c + d)) → ⊥
  illegal~⊔3L {a} {b} {c} {d} = λ ()

  illegal~⊔3R : ∀ {a b c d} → a ~ b ⊔ suc (suc (suc b + c + d)) → ⊥
  illegal~⊔3R {a} {b} {c} {d} = λ ()

  gJoinRight : {hr x : ℕ} {@0 l u : Key⁺}
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

  ... | right .hc k = ⊥-elim (illegal~⊔3R b )
  ... | 1-offR .hc = ⊥-elim (illegal~⊔2R b)

  gJoinLeft : {hl x : ℕ} {@0 l u : Key⁺}
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
      T' = 1# , node p l c ~0

  ... | 1-offR .hc = ⊥-elim (illegal~⊔2L b)
  ... | right .hc k = ⊥-elim (illegal~⊔3L b)

  gJoin : {hl hr : ℕ} {@0 l u : Key⁺}
          → ((k , v) : Key × V)
          → BOBMap V l [ k ] hl
          → BOBMap V [ k ] u hr
          → ∃ λ i → BOBMap V l u (i ⊕ max hl hr)
  gJoin {hl} {hr} p l r
    with compareBalance hl hr
  ... | left     .hr k rewrite lemRR+n {k} {hr} = gJoinRight p l r
  ... | 1-offL   .hr   rewrite lem4L {hr} = 1# , node p l r ~-
  ... | balanced .hl   rewrite lemC {hl}  = 1# , node p l r ~0
  ... | 1-offR   .hl   rewrite lem4R {hl} = 1# , node p l r ~+
  ... | right    .hl k rewrite lemLL+n {k} {hl} = gJoinLeft p l r

  -- * SPLIT STARTS HERE -----------------------------------------------------

  n≤n : ∀ {n} → n ≤ n
  n≤n {n} = ≤-refl

  n≤sn : ∀ {n} → n ≤ suc n
  n≤sn {n} = <⇒≤ (n<1+n n)

  record Split (x : Key) (@0 l u : Key⁺) (@0 h : ℕ) : Set (k ⊔ v ⊔ ℓ₁) where
    constructor split
    field
      value : Maybe V
      leftH : ℕ
      @0 leftP : leftH ≤ h
      leftT : BOBMap V l [ x ] leftH
      rightH : ℕ
      @0 rightP : rightH ≤ h
      rightT : BOBMap V [ x ] u rightH

  bigbal : ∀ {a b c}
          → a ~ b ⊔ c
          → (a ≡ c × b ≡ a)
            ⊎ (a ≡ c × a ≡ suc b)
            ⊎ (b ≡ c × b ≡ suc a)
  bigbal ~+ = inr (inr (refl , refl))
  bigbal ~0 = inl (refl , refl)
  bigbal ~- = inr (inl (refl , refl))

  -- TODO: Talk about this
  lembal : ∀ {a b c}
           → a ~ b ⊔ c
           → (a < c × b ≤ c)
             ⊎ (a ≤ c × b < c)
             ⊎ (a ≤ c × b ≤ c)
  lembal {a} {b} {c} bal with bigbal bal
  -- LOL!! LOL!! LOL!!
  ... | inl (refl , refl) = inr (inr (n≤n , n≤n))
  ... | inr (inl (refl , refl)) = inr (inl (n≤n , n≤n))
  ... | inr (inr (refl , refl)) = inl (n≤n , n≤n)

  lem≤max : ∀ {a b c} → a ≤ c → b ≤ c → max a b ≤ c
  lem≤max p1 p2 = ⊔-lub p1 p2

  lemin : ∀ {@0 l u} {h : ℕ}
          → {x : Key}
          → {m : BOBMap V l u h}
          → x ∈ m
          → ∃ λ n → suc n ≡ h
  lemin {h = h} {x = x} {m = leaf} ()
  lemin {h = suc h} {m = node (x , _) l r b} _ = h , refl

  -- what the hell??
  sa≤b⇒a≤sb : ∀ {a b} → suc a ≤ b → a ≤ suc b
  sa≤b⇒a≤sb {a} {b} prf = s≤s⁻¹ (m≤n⇒m≤1+n (m≤n⇒m≤1+n prf))

  data SplitPartL {@0 l u : Key⁺} (@0 sh : ℕ) (x : Key) : Set (k ⊔ v ⊔ ℓ₁) where
    ltI : (hl' : ℕ) → (@0 prf : hl' ≤ sh) → BOBMap V l [ x ] hl' → SplitPartL sh x

  data SplitPartR {@0 l u : Key⁺} (@0 sh : ℕ) (x : Key) : Set (k ⊔ v ⊔ ℓ₁) where
    rtI : (hr' : ℕ) → (@0 prf : hr' ≤ sh) → BOBMap V [ x ] u hr' → SplitPartR sh x

  splitAt : ∀ {@0 l u} {h : ℕ}
             → (k : Key)
             → {{@erased l<k : l <⁺ [ k ]}} → {{@erased k<u : [ k ] <⁺ u}}
             → (m : BOBMap V l u h)
             → Split k l u h
  splitAt {ₗ} {ᵘ} {zero} k leaf
    = split nothing 0 z≤n leaf 0 z≤n leaf

  splitAt {h = suc h} k (node (k' , v') l r b) with compare k k'
  splitAt {ₗ} {ᵘ} {h} k {{l<k = l<k}} (node {hl = hl} {hr = hr} (k' , v') l r b)
    | tri< x _ _ = case lt of λ where
      (ltI lh lp lt) → case rt of λ where
        (rtI rh rp rt) →
          split (Split.value leftS)
            lh lp lt
            rh rp rt
    where
      sh : ℕ
      sh = h

      leftS : Split k ₗ [ k' ] hl
      leftS = splitAt k {{l<k}} {{[ x ]ᴿ}} l

      lt : SplitPartL {ₗ} {ᵘ} sh k --∃ λ hl' → hl' ≤ sh × BOBMap V ₗ [ k ] hl'
      lt with lembal b
      lt | inr (inr (o , _))
        = ltI (Split.leftH leftS) (≤-trans (Split.leftP leftS) (m≤n⇒m≤1+n o)) (Split.leftT leftS)
      lt | inr (inl (o , _))
        = ltI (Split.leftH leftS) (≤-trans (Split.leftP leftS) (m≤n⇒m≤1+n o)) (Split.leftT leftS)
      lt | inl (o , _)
        = ltI (Split.leftH leftS) (≤-trans (Split.leftP leftS) (sa≤b⇒a≤sb o)) (Split.leftT leftS)

      -- a bit (very) convoluted, surely there are better ways to do this
      -- also uses a few lemmas which are not proven yet
      rt : SplitPartR {ₗ} {ᵘ} sh k --∃ λ hr' → hr' ≤ sh × BOBMap V [ k ] ᵘ hr'
      rt with leftS
      rt | split _ _ _ _ ht ht<hl t with gJoin (k' , v') t r
      rt | split _ _ _ _ ht ht<hl t | 0# , β with lembal b
      ... | inl (hl<h , hr≤h)
        = rtI (max ht hr) (lem≤max (≤-trans ht<hl (sa≤b⇒a≤sb hl<h)) (m≤n⇒m≤1+n hr≤h)) β
      -- max ht hr , lem≤max (≤-trans ht<hl (m≤n⇒m≤1+n hl<h)) (m≤n⇒m≤1+n hr<h) , β
      ... | inr (inl (hl≤h , hr<h))
        = rtI (max ht hr) (lem≤max (≤-trans ht<hl (m≤n⇒m≤1+n hl≤h)) (sa≤b⇒a≤sb hr<h)) β
      ... | inr (inr (hl≤h , hr≤h))
        = rtI (max ht hr) (lem≤max (≤-trans ht<hl (m≤n⇒m≤1+n hl≤h)) (m≤n⇒m≤1+n hr≤h)) β
      rt | split _ _ _ _ ht ht<hl t | 1# , β with lembal b
      ... | inl (hl<h , hr≤h)
        = rtI (suc (max ht hr))
              (s≤s (lem≤max (≤-trans ht<hl (s≤s⁻¹ (m≤n⇒m≤1+n hl<h))) hr≤h))
              β
      ... | inr (inl (hl≤h , hr<h))
        = rtI (suc (max ht hr))
              (s≤s (lem≤max (≤-trans ht<hl hl≤h) (s≤s⁻¹ (m≤n⇒m≤1+n hr<h))))
              β
      ... | inr (inr (hl≤h , hr≤h))
        = rtI (suc (max ht hr))
              (s≤s (lem≤max (≤-trans ht<hl hl≤h) hr≤h))
              β

  splitAt {ₗ} {ᵘ} {h} k (node {hl = hl} {hr = hr} (.k , v') l r b)
    | tri≈ _ refl _ = split (just v')
                            hl (proj₁ lt) (proj₂ lt)
                            hr (proj₁ rt) (proj₂ rt)
    where
      sh : ℕ
      sh = h

      lt : hl ≤ sh × BOBMap V ₗ [ k ] hl
      lt with lembal b
      ... | inl (o , u) = sa≤b⇒a≤sb o , l
      ... | inr (inl (o , _)) = (m≤n⇒m≤1+n o) , l
      ... | inr (inr (o , _)) = (m≤n⇒m≤1+n o) , l

      rt : hr ≤ sh × BOBMap V [ k ] ᵘ hr
      rt with lembal b
      ... | inl (_ , p) = m≤n⇒m≤1+n p , r
      ... | inr (inl (o , u)) = m≤n⇒m≤1+n (<⇒≤ u) , r
      ... | inr (inr (o , u)) = m≤n⇒m≤1+n u , r

  splitAt {ₗ} {ᵘ} {h} k {{k<u = k<u}} (node {hl = hl} {hr = hr} (k' , v') l r b)
    | tri> _ _ x = case lt of λ where
      (ltI lh lp lt) → case rt of λ where
        (rtI rh rp rt) →
          split (Split.value rightS)
            lh lp lt
            rh rp rt
    where
      sh : ℕ
      sh = h

      rightS : Split k [ k' ] ᵘ hr
      rightS = splitAt k {{[ x ]ᴿ}} r

      rt : SplitPartR {ₗ} {ᵘ} sh k --∃ λ hr' → hr' ≤ sh × BOBMap V [ k ] ᵘ hr'
      rt with lembal b
      rt | inl (_ , o) with rightS
      ... | split _ _ _ _ ht ht<hr t = rtI ht (≤-trans ht<hr (m≤n⇒m≤1+n o)) t
      rt | inr (inl (o , u)) with rightS
      ... | split _ _ _ _ ht ht<hr t = rtI ht (≤-trans ht<hr (sa≤b⇒a≤sb u)) t
      rt | inr (inr (o , u)) with rightS
      ... | split _ _ _ _ ht ht<hr t = rtI ht (≤-trans ht<hr (m≤n⇒m≤1+n u)) t

      lt : SplitPartL {ₗ} {ᵘ} sh k --∃ λ hl' → hl' ≤ sh × BOBMap V ₗ [ k ] hl'
      lt with rightS
      lt | split _ ht ht<hr t _ _ _ with gJoin (k' , v') l t
      lt | split _ ht ht<hr t _ _ _ | 0# , β with lembal b
      ... | inl (hl<h , hr≤h) = ltI
          (max hl ht)
          (lem≤max (sa≤b⇒a≤sb hl<h) (≤-trans ht<hr (m≤n⇒m≤1+n hr≤h)))
          β
      ... | inr (inl (hl≤h , hr<h)) = ltI
          (max hl ht)
          (lem≤max (m≤n⇒m≤1+n hl≤h) (≤-trans ht<hr (sa≤b⇒a≤sb hr<h)))
          β
      ... | inr (inr (hl≤h , hr≤h)) = ltI
          (max hl ht)
          (lem≤max (m≤n⇒m≤1+n hl≤h) (≤-trans ht<hr (m≤n⇒m≤1+n hr≤h)))
          β
      lt | split _ ht ht<hr t _ _ _ | 1# , β with lembal b
      ... | inl (hl<h , hr≤h) = ltI
          (suc (max hl ht))
          (s≤s (lem≤max (s≤s⁻¹ (m≤n⇒m≤1+n hl<h)) (≤-trans ht<hr hr≤h)))
          β
      ... | inr (inl (hl≤h , hr<h)) = ltI
          (suc (max hl ht))
          (s≤s (lem≤max hl≤h (≤-trans ht<hr (s≤s⁻¹ (m≤n⇒m≤1+n hr<h)))))
          β
      ... | inr (inr (hl≤h , hr≤h)) = ltI
          (suc (max hl ht))
          (s≤s (lem≤max hl≤h (≤-trans ht<hr hr≤h)))
          β

  -- * UNION STARTS HERE -----------------------------------------------------
{-
  sa+n : ∀ {a n} → suc (a + n) ≡ a + suc n
  sa+n {zero} {zero} = refl
  sa+n {zero} {suc n} = refl
  sa+n {suc a} {n} rewrite sa+n {a} {n} = refl

  ≤+n : ∀ {a b n} → a ≤ b → a ≤ b + n
  ≤+n {zero} {b} {n} p = z≤n
  {-# CATCHALL #-}
  ≤+n {a} {b} {zero} p rewrite n+0 b = p
  {-# CATCHALL #-}
  ≤+n {a} {b} {suc n} p with m≤n⇒m≤1+n (≤+n {a} {b} {n} p)
  ... | x rewrite sa+n {b} {n} = x

  lemgt : ∀ {a b c n} → b ≤ c → a ≡ c + n → max a b ≡ c + n
  lemgt {a} {b} {c} {n} p1 p2 with ≤+n {n = n} p1
  ... | x rewrite p2 with m≤n⇒m⊔n≡n x
  ... | y rewrite ⊔-comm b (c + n) = y
-}
  n⊔n≡n : ∀ n → max n n ≡ n
  n⊔n≡n n = lemC {n}
{-
  mab≡mba : ∀ a b → max a b ≡ max b a
  mab≡mba a b = ⊔-comm a b

  lemm : ∀ {a b} → b ≤ a → max a b ≡ a
  lemm {zero} {zero} p1 = refl
  lemm {suc a} {zero} p1 = refl
  lemm {suc a} {suc b} (s≤s p1) rewrite lemm p1 = refl

  lemm' : ∀ {a b} → b ≤ a → max b a ≡ a
  lemm' {zero} {zero} p1 = refl
  lemm' {suc a} {zero} p1 = refl
  lemm' {suc a} {suc b} (s≤s p1) = n≡n⇒sn≡sn (lemm' p1)

  ⊔-0 : ∀ {n} → max n zero ≡ n
  ⊔-0 {zero} = refl
  ⊔-0 {suc n} = refl

  lemm+n : ∀ {a b n} → b ≤ a → max (a + n) b ≡ a + n
  lemm+n {zero} {zero} {n} p1 = ⊔-0 {n}
  lemm+n {suc a} {zero} {n} p1 = refl
  lemm+n {suc a} {suc b} {n} (s≤s p1) with b ≤? a
  ... | yes x rewrite lemm+n {a} {b} {n} x = refl
  ... | no  x = contradiction p1 x

  n≢sn : ∀ {n} → ¬ n ≡ suc n
  n≢sn {n} ()

  sa≰sb⇒a≰b : ∀ {a b} → ¬ (suc a) ≤ (suc b) → ¬ a ≤ b
  sa≰sb⇒a≰b {a} {b} sa≰sb a≤b = contradiction (s≤s a≤b) sa≰sb

  a≰b∧a≤sb⇒a=sb : ∀ {a b} → ¬ a ≤ b → a ≤ suc b → a ≡ suc b
  a≰b∧a≤sb⇒a=sb {zero} {b} p1 p2 = ⊥-elim (p1 z≤n)
  a≰b∧a≤sb⇒a=sb {suc a} {zero} p1 p2
    rewrite n≤0⇒n≡0 (s≤s⁻¹ p2) = refl
  a≰b∧a≤sb⇒a=sb {suc a} {suc b} p1 p2
    rewrite a≰b∧a≤sb⇒a=sb {a} {b} (sa≰sb⇒a≰b p1) (s≤s⁻¹ p2) = refl

  postulate
    a+sb≡sc⇒a+b≡c : ∀ {a b c} → a + suc b ≡ suc c → c ≡ a + b

  lemA : ∀ {hlʳ hrʳ hl n hL hR}
         → hlʳ ~ hrʳ ⊔ hl + n
         → hL ≤ hl
         → hR ≤ hl
         → max hlʳ hL ~ max hrʳ hR ⊔ hl + n
  lemA {hlʳ} {hrʳ} {hl} {zero} {hL} {hR} b hl<hl hr<hl
    rewrite n+0 hl with bigbal b
  ... | inl (refl , refl)
    rewrite lemm hl<hl rewrite lemm hr<hl = b
  ... | inr (inl (refl , refl))
    rewrite lemm hl<hl rewrite lemm hr<hl = fun
    where
      fun : suc hrʳ ~ max hrʳ hR ⊔ suc hrʳ
      fun with hR ≤? hrʳ
      ... | yes x rewrite lemm x = ~-
      ... | no  x rewrite a≰b∧a≤sb⇒a=sb x hr<hl rewrite lem4R {hrʳ} = ~0
  ... | inr (inr (refl , refl))
    rewrite lemm hl<hl rewrite lemm hr<hl = fun
    where
      fun : max hlʳ hL ~ suc hlʳ ⊔ suc hlʳ
      fun with hL ≤? hlʳ
      ... | yes x rewrite lemm x = b
      ... | no  x rewrite a≰b∧a≤sb⇒a=sb x hl<hl rewrite lem4R {hlʳ} = ~0
  lemA {hlʳ} {hrʳ} {hl} {suc n} {hL} {hR} b hl<hl hr<hl
    with bigbal b
  ... | inl (refl , refl)
    rewrite lemm+n {n = suc n} hl<hl rewrite lemm+n {n = suc n} hr<hl = b
  ... | inr (inl (refl , t))
    rewrite lemm+n {n = suc n} hl<hl
    rewrite a+sb≡sc⇒a+b≡c t
    rewrite lemm+n {n = n} hr<hl = b
  ... | inr (inr (refl , t))
    rewrite lemm+n {n = suc n} hr<hl
    rewrite a+sb≡sc⇒a+b≡c t
    rewrite lemm+n {n = n} hl<hl = b

  postulate
    tttt : ∀ {a b n} → a + suc n ≡ suc b → a + n ≡ b
    pppp : ∀ {a b c n} → c + n ≡ a → b ≤ c → max a b ≡ a

  ssss : ∀ {a b c n}
         → c + n ≡ suc a
         → b ≤ c
         → suc (max a b) ≡ c + n ⊎ suc (max a b) ≡ suc c + n
  ssss {a} {b} {c} {zero} c0=sa b<c
    rewrite n+0 c
    rewrite c0=sa
    with b ≤? a
  ... | yes x
    rewrite lemm x = inl refl
  ... | no  x
    rewrite a≰b∧a≤sb⇒a=sb x b<c
    rewrite lem4R {a}
    = inr refl
  ssss {a} {b} {c} {suc n} c0=sa b<c
    rewrite c0=sa
    with b ≤? a
  ... | yes x
    rewrite lemm x = inl refl
  ... | no  x
    rewrite pppp (tttt c0=sa) b<c
    = inl refl

  sss2 : ∀ {a b c n}
         → c + n ≡ suc a
         → b ≤ c
         → max (suc a) (max a b) ≡ suc a
  sss2 {a} {b} {c} c0=sa b<c with ssss c0=sa b<c
  ... | inr x
    rewrite n+0 c
    rewrite suc-injective x
    rewrite c0=sa
    rewrite n⊔n≡n a
    = refl
  ... | inl x
    rewrite n+0 c
    rewrite c0=sa
    rewrite suc-injective x
    rewrite lem4L {a}
    = refl

  suc≡≤ : ∀ {n m} → n ≡ suc m → m ≤ n
  suc≡≤ {.(suc m)} {m} refl = n≤1+n m

  sss2L : ∀ {a b c n}
          → c + n ≡ suc a
          → b ≤ c
          → max (max a b) (suc a) ≡ suc a
  sss2L {a} {b} {c} p1 p2 with sss2 p1 p2
  ... | x rewrite mab≡mba (max a b) (suc a) = x

  ≤suc : ∀ {n m} → n ≤ m → n ≤ (suc m)
  ≤suc z≤n = z≤n
  ≤suc (s≤s prf) = s≤s (≤suc prf)

  fixHeight1# : ∀ {n hlʳ hrʳ hl hR hL}
    → hlʳ ~ hrʳ ⊔ hl + n
    → hR ≤ hl
    → hL ≤ hl
    → max (suc (max hlʳ hL)) (1# ⊕ max hrʳ hR) ≡ suc (hl + n)
  fixHeight1# {n} {hl = hl} bal prfR prfL with bigbal (lemA bal prfL prfR)
  ... | inl (fst , snd) rewrite fst rewrite snd rewrite n⊔n≡n (hl + n) = refl
  ... | inr (inl (fst , snd)) rewrite fst rewrite lemm (suc≡≤ snd) = refl
  ... | inr (inr (fst , snd)) rewrite fst rewrite lemm' (suc≡≤ snd) = refl

  m⊔sm⇒sm : ∀ {m} → max (suc m) m ≡ suc m
  m⊔sm⇒sm {zero} = refl
  m⊔sm⇒sm {suc m} rewrite m⊔sm⇒sm {m} = refl

  fixMapUR : ∀ {n hlʳ hrʳ hl hR hL} {l u : Key⁺}
    → (k : Key)
    → (f : V → Maybe V → V)
    → (v : V)
    → (value : Maybe V)
    → hlʳ ~ hrʳ ⊔ hl + n
    → hR ≤ hl
    → hL ≤ hl
    → BOBMap V l [ k ] (suc (max hlʳ hL))
    → ∃ (λ j → BOBMap V [ k ] u (j ⊕ max hrʳ hR))
    → ∃ (λ i → BOBMap V l u (i ⊕ suc (hl + n)))
  fixMapUR k f v value bal prfR prfL t1 (j , t2) with bigbal (lemA bal prfL prfR)
  fixMapUR {n} {hl = hl} k f v value bal prfR prfL t1 (j , t2)
    | inl (fst , snd) rewrite fst rewrite snd with gJoin (k , f v value) t1 t2
  ... | i , t with j
  ... | 0# rewrite m⊔sm⇒sm {hl + n} = i , t
  ... | 1# rewrite n⊔n≡n (hl + n) = i , t
  fixMapUR {hrʳ = hrʳ} {hR = hR} k f v value bal prfR prfL t1 (j , t2)
    | inr (inl (fst , snd)) rewrite fst with gJoin (k , f v value) t1 t2
  ... | i , t with j
  ... | 0# rewrite snd rewrite lemRR {max hrʳ hR} = i , t
  ... | 1# rewrite lemm (suc≡≤ snd) = i , t
  fixMapUR {n} {hl = hl} k f v value bal prfR prfL t1 (j , t2)
    | inr (inr (fst , snd)) rewrite fst with j
  ... | 0# rewrite snd = joinʳ⁺ (k , f v value) t1 (0# , t2) ~0
  ... | 1# with gJoin (k , f v value) t1 t2
  ... | i , t rewrite lemm' (suc≡≤ snd) = i , t

  lemA' : ∀ {hlʳ hrʳ hL hR hl n : ℕ}
      → hlʳ ~ hrʳ ⊔ hl + n
      → hL ≤ hl → hR ≤ hl
      → max hL hlʳ ~ max hR hrʳ ⊔ hl + n
  lemA' {hlʳ} {hrʳ} {hL} {hR} bal prfL prfR rewrite ⊔-comm hL hlʳ rewrite ⊔-comm hR hrʳ = lemA bal prfL prfR

  ≤or≡ : ∀ {n m} → n ≤ suc m → n ≤ m ⊎ (n ≡ suc m)
  ≤or≡ {.zero} {m} z≤n = inl z≤n
  ≤or≡ {.1} {zero} (s≤s {zero} prf) = inr refl
  ≤or≡ {suc zero} {suc m} (s≤s prf) = inl (s≤s z≤n)
  ≤or≡ {suc (suc n)} {suc m} (s≤s prf) with ≤or≡ prf
  ... | inl x = inl (s≤s x)
  ... | inr refl = inr refl

  lemA0 : ∀ {hlʳ hrʳ hL hR hl : ℕ}
      → hlʳ ~ hrʳ ⊔ hl
      → hL ≤ suc hl → hR ≤ suc hl
      → max hL hlʳ ~ max hR hrʳ ⊔ hl
  lemA0 bal prfL prfR with ≤or≡ prfL
  ... | inl x = {!!}
  ... | inr refl with ≤or≡ prfR
  ... | inl x = {!!}
  ... | inr refl = {!!}

  lemASuc : ∀ {hlʳ hrʳ hL hR hl n : ℕ}
      → hlʳ ~ hrʳ ⊔ hl
      → hL ≤ suc (hl + n) → hR ≤ suc (hl + n)
      → max hL hlʳ ~ max hR hrʳ ⊔ suc (hl + n)
  lemASuc bal prfL prfR = {!!}

  fixHeight : ∀ i j {h₁ h₂ hl hr hR hL}
    → hl ~ hr ⊔ h₂
    → hR ≤ (suc h₁)
    → hL ≤ (suc h₁)
    → suc (max h₁ h₂) ≡ max (i ⊕ max hL hl) (j ⊕ max hR hr)
  fixHeight 0# 0# bal prfR prfL = {!!}
  fixHeight 0# 1# bal prfR prfL = {!!}
  fixHeight 1# 0# bal prfR prfL = {!!}
  fixHeight 1# 1# bal prfR prfL = {!!}

  fixMap : ∀ {i h₁ h₂ hl hr hR hL} {l u : Key⁺}
    → (k : Key)
    → (f : V → Maybe V → V)
    → (v : V)
    → (value : Maybe V)
    → hl ~ hr ⊔ h₂
    → hR ≤ (suc h₁)
    → hL ≤ (suc h₁)
    → BOBMap V l [ k ] (i ⊕ (max hL hl))
    → ∃ (λ j → BOBMap V [ k ] u (j ⊕ max hR hr))
    → ∃ (λ k → BOBMap V l u (k ⊕ suc (max h₁ h₂)))
  fixMap {i} {h₁} {h₂} k f v v' bal prfR prfL t1 (j , t2) with compareℕ h₁ h₂
  ---- h₁ < h₂ ----
  fixMap {0#} {h₁} {h₂} k f v v' bal prfR prfL t1 (j , t2)
    | Ordℕ.less .h₁ n rewrite lemL {n} {h₁} = joinʳ⁺ (k , f v v') t1 (j , t2) (lemA' bal prfL prfR)
  fixMap {1#} {h₁} {h₂} {hl} {hr} {hL} {hR} k f v v' bal prfR prfL t1 (j , t2)
    | Ordℕ.less .h₁ n rewrite lemL {n} {h₁}
      rewrite ⊔-comm hR hl rewrite ⊔-comm hL hr
      = fixMapUR k f v v' bal prfR prfL t1 (j , t2)
  ---- h₁ ≡ h₂ ----
  fixMap {0#} {h₁} {.h₁} k f v v' bal prfR prfL t1 (j , t2)
    | Ordℕ.equal .h₁ rewrite n⊔n≡n h₁ = joinʳ⁺ (k , f v v') t1 (j , t2) (lemA0 bal prfL prfR)
  fixMap {1#} {h₁} {.h₁} k f v v' bal prfR prfL t1 (j , t2)
    | Ordℕ.equal .h₁ rewrite n⊔n≡n h₁ = {!gJoin (k , f v v') t1 t2!}
  ---- h₁ > h₂ ----
  fixMap {0#} {h₁} {h₂} k f v v' bal prfR prfL t1 (j , t2)
    | Ordℕ.greater .h₂ n rewrite lemR {n} {h₂} = joinʳ⁺ (k , f v v') t1 (j , t2) {!lemASuc bal  !}
  fixMap {1#} {h₁} {h₂} k f v v' bal prfR prfL t1 (j , t2)
    | Ordℕ.greater .h₂ n rewrite lemR {n} {h₂} = {!!}
-}
  -- UNION ------------------------------------------------------
{-
  union : {h1 h2 : ℕ} → ∀ {l u}
          → (V → Maybe V → V)
          → BOBMap V l u h1
          → BOBMap V l u h2
          → ∃ λ n → BOBMap V l u (n ⊕ max h1 h2)
  union f leaf n@leaf = 0# , (leaf ⦃ mklim n ⦄)
  union f leaf n@(node _ _ _ _) = 0# , n
  union f m@(node _ _ _ _) leaf = 0# , m
  union f m@(node _ _ _ _) n@(node (k , v) lt rt bal) with splitAt k ⦃ mklim lt ⦄ ⦃ mklim rt ⦄ m
  ... | split value (hL , prfL , treeL) (hR , prfR , treeR) with union f treeL lt
  ... | i , t1 with union f treeR rt
  ... | j , t2 rewrite fixHeight i j bal prfR prfL = gJoin (k , f v value) t1 t2 -- fixMap {i} k f v value bal prfR prfL t1 (union f treeR rt)
-}
  baltomax : ∀ a b c → a ~ b ⊔ c → max a b ≡ c
  baltomax a .(1 + a) .(1 + a) ~+ = n⊔sn≡sn a
  baltomax a .a .a ~0 = n⊔n≡n a
  baltomax .(1 + b) b .(1 + b) ~- rewrite ⊔-comm (suc b) b = n⊔sn≡sn b

  balto≤ : ∀ a b c → a ~ b ⊔ c → a ≤ c × b ≤ c
  balto≤ _ _ _ ~+ = (m≤n⇒m≤1+n ≤-refl) , ≤-refl
  balto≤ _ _ _ ~0 = ≤-refl , ≤-refl
  balto≤ _ _ _ ~- = ≤-refl , (m≤n⇒m≤1+n ≤-refl)

  @0 ubound : (s₁ s₂ hl hr hL hR uL uR : ℕ) → (i : ℕ₂)
    → hl ~ hr ⊔ s₂
    → hL ≤ suc s₁
    → hR ≤ suc s₁
    → uL ≤ hL + hl
    → uR ≤ hR + hr
    → i ⊕ max uL uR ≤ (suc s₁ + suc s₂)
  ubound s₁ s₂ hl hr hL hR uL uR 0# b p1 p2 p3 p4
    with balto≤ hl hr s₂ b
  ... | fst , snd
    with a≤b⇒a+c≤b+c p1 hl , a≤b⇒a+c≤b+c p2 hr
  ... | xx , yy rewrite ⊔-comm uL uR
    = ⊔-lub (≤-trans p4 (a≤b+c≤d⇒a+c≤b+d hR (suc s₁) hr (suc s₂) p2 (m≤n⇒m≤1+n snd)))
            (≤-trans p3 (a≤b+c≤d⇒a+c≤b+d hL (suc s₁) hl (suc s₂) p1 (m≤n⇒m≤1+n fst)))
  ubound s₁ s₂ hl hr hL hR uL uR 1# b p1 p2 p3 p4
    with balto≤ hl hr s₂ b
  ... | fst , snd
    with a≤b⇒a+c≤b+c p1 hl , a≤b⇒a+c≤b+c p2 hr
  ... | xx , yy rewrite c+sb≡sc+b s₁ s₂ rewrite ⊔-comm uL uR
    = s≤s (⊔-lub (≤-trans p4 (a≤b+c≤d⇒a+c≤b+d hR (suc s₁) hr s₂ p2 snd))
                 (≤-trans p3 (a≤b+c≤d⇒a+c≤b+d hL (suc s₁) hl s₂ p1 fst)))

  -- Given a lower bound of max h1 h2 ≤ h where h is the output height and
  -- h1 & h2 are input heights it is not possible to prove it with the
  -- existing information.
  -- The furthest I can get is
  --   max hR hr ≤ suc (max s₁ s₂)
  --   max hL hl ≤ suc (max s₁ s₂)
  -- but this does not help showing that suc (max s₁ s₂) ≤ max uL uR as we
  -- know nothing about the relation of uL/uR and s₁/s₂.
  lbound : (s₁ s₂ hl hr hL hR uL uR : ℕ)
    → hl ~ hr ⊔ s₂
    → (∃ λ i → i ⊕ s₁ ≡ max hL hR)
--    → hL ≤ suc s₁
--    → hR ≤ suc s₁
    → max hL hl ≤ uL
    → max hR hr ≤ uR
    → max s₁ s₂ ≤ max uL uR
  lbound s₁ s₂ hl hr hL hR uL uR b (0# , p1) p3 p4 with baltomax hl hr s₂ b
  ... | xx rewrite sym xx | p1 | testo hL hl hR hr
    = testo2 (max hL hl) uL (max hR hr) uR p3 p4
  lbound s₁ s₂ hl hr hL hR uL uR b (1# , p1) p3 p4 = {!!}

  record UnionReturn {@0 l u : Key⁺} {h1 h2 : ℕ}
                     (@0 t₁ : BOBMap V l u h1) (@0 t₂ : BOBMap V l u h2) : Set (k ⊔ v ⊔ ℓ₁) where
    constructor retval
    field
      hof : ℕ
      tree : BOBMap V l u hof
      @0 prf : hof ≤ (h1 + h2)

  eqto≤ : ∀ n → n ≤ n → n ≤ n + 0
  eqto≤ n p rewrite n+0 n = ≤-refl

  union-loose : {h1 h2 : ℕ} → {@0 l u : Key⁺}
    → (V → Maybe V → V)
    → (t1 : BOBMap V l u h1)
    → (t2 : BOBMap V l u h2)
    → UnionReturn t1 t2
--    → ∃ λ h
--      → BOBMap V l u h × h ≤ (h1 + h2)
  union-loose {h1} {h2} f leaf t = retval h2 t ≤-refl
  union-loose {h1} f t leaf = retval h1 t (eqto≤ h1 ≤-refl)
  union-loose {suc s₁} {suc s₂} f t₁@(node p₁ l₁ r₁ b₁) t₂@(node p₂ l₂ r₂ b₂)
    with splitAt (proj₁ p₂) {{mklim l₂}} {{mklim r₂}} t₁
  union-loose {suc s₁} {suc s₂} f t₁@(node p₁ l₁ r₁ b₁) t₂@(node {hl} {hr} p₂ l₂ r₂ b₂)
    | split value hL prfL treeL hR prfR treeR
    with union-loose f treeL l₂
  ... | retval uL tL plL with union-loose f treeR r₂
  ... | retval uR tR plR with gJoin (proj₁ p₂ , f (proj₂ p₂) value) tL tR
  ... | i , t = retval
                  (i ⊕ max uL uR)
                  t
                  (ubound s₁ s₂ hl hr hL hR uL uR i b₂ prfL prfR plL plR)

  -- * DELETE STARTS HERE ----------------------------------------------------

  delete : ∀ {@0 l u : Key⁺} {h : ℕ} (k : Key)
           {{@erased l≤p : l <⁺ [ k ]}} {{@erased p≤u : [ k ] <⁺ u}}
           → BOBMap V l u h
           → ∃ λ i → BOBMap V l u pred[ i ⊕ h ]
  delete k leaf = 0# , leaf
  delete k (node p lt rt bal) with compare k (proj₁ p)
  ... | tri< k<p _ _ = joinˡ⁻ p (delete k {{p≤u = [ k<p ]ᴿ}} lt) rt bal
  ... | tri≈ _ refl _ = join lt rt bal
  ... | tri> _ _ p<k = joinʳ⁻ p lt (delete k {{[ p<k ]ᴿ}} rt) bal

  -- Validity of the insert + lookup operations should come from the map that
  -- they are decorating. In other words allInsert is correct since it mimics
  -- insert which is proven correct.
  -- Maybe a bit of a weak argument but its the best I have got.
  -- And allLookup is correct since it uses a membership proof for the lookup
  -- just like lookup∈
  data All (P : Pred (Key × V) ℓₐ) {@0 l u : Key⁺}
      : ∀ {@0 h : ℕ} → BOBMap V l u h → Set (k ⊔ ℓ₁ ⊔ v ⊔ ℓₐ) where
    leaf : ⦃ @erased l<u : l <⁺ u ⦄ → All P leaf
    node : ∀ {hl hr h}
           → {p : Key × V}
           (let (k , v) = p)
           {lt : BOBMap V l [ k ] hl}
           {rt : BOBMap V [ k ] u hr}
           {bal : hl ~ hr ⊔ h}
           → P (k , v)
           → All P lt
           → All P rt
           → All P (node (k , v) lt rt bal)

  allLookup : {@0 l u : Key⁺} {@0 h : ℕ} {m : BOBMap V l u h} {k : Key} {v : V} {P : Pred (Key × V) ℓₐ}
    → Any (λ v' → v ≡ v') k  m
    → All P m
    → P (k , v)
  allLookup (here refl) (node p lt rt) = p
  allLookup (left prf) (node p lt rt) = allLookup prf lt
  allLookup (right prf) (node p lt rt) = allLookup prf rt

  alljoinᴸ : ∀ {@0 l u : Key⁺} {hl hr h : ℕ} {P : Pred (Key × V) ℓₐ}
    → {k : Key} {v : V}
    → {lt⁺ : ∃ λ i → BOBMap V l [ k ] (i ⊕ hl)}
    → {rt : BOBMap V [ k ] u hr}
    → P (k , v)
    → All P (proj₂ lt⁺)
    → All P rt
    → (bal : hl ~ hr ⊔ h)
    → All P (proj₂ (joinˡ⁺ (k , v) lt⁺ rt bal))
  alljoinᴸ {lt⁺ = (0# , lt)} p allL allR bal = node p allL allR
  alljoinᴸ {lt⁺ = (1# , lt)} p allL allR ~+ = node p allL allR
  alljoinᴸ {lt⁺ = (1# , lt)} p allL allR ~0 = node p allL allR
  alljoinᴸ {lt⁺ = (1# , node _ _ _ ~0)} p (node a aL aR) allR ~- = node a aL (node p aR allR)
  alljoinᴸ {lt⁺ = (1# , node _ _ _ ~-)} p (node a aL aR) allR ~- = node a aL (node p aR allR)
  alljoinᴸ {lt⁺ = (1# , node _ _ (node _ _ _ _) ~+)} {rt} p (node a aL (node aᴿ aLᴿ aRᴿ)) allR ~- =
    node aᴿ (node a aL aLᴿ) (node p aRᴿ allR)

  alljoinᴿ : ∀ {@0 l u : Key⁺} {hl hr h : ℕ} {P : Pred (Key × V) ℓₐ}
    → {k : Key} {v : V}
    → {lt : BOBMap V l [ k ] hl}
    → {rt⁺ : ∃ λ i → BOBMap V [ k ] u (i ⊕ hr)}
    → P (k , v)
    → All P lt
    → All P (proj₂ rt⁺)
    → (bal : hl ~ hr ⊔ h)
    → All P (proj₂ (joinʳ⁺ (k , v) lt rt⁺ bal))
  alljoinᴿ {rt⁺ = (0# , rt)} p allL allR bal = node p allL allR
  alljoinᴿ {rt⁺ = (1# , rt)} p allL allR ~0 = node p allL allR
  alljoinᴿ {rt⁺ = (1# , rt)} p allL allR ~- = node p allL allR
  alljoinᴿ {rt⁺ = (1# , (node _ _ _ ~+))} p allL (node a aL aR) ~+ = node a (node p allL aL) aR
  alljoinᴿ {rt⁺ = (1# , (node _ _ _ ~0))} p allL (node a aL aR) ~+ = node a (node p allL aL) aR
  alljoinᴿ {rt⁺ = (1# , (node _ (node _ _ _ _) _ ~-))} p allL (node a (node aᴸ aLᴸ aRᴸ) aR) ~+ =
    node aᴸ (node p allL aLᴸ) (node a aRᴸ aR)

  allInsert : {@0 l u : Key⁺} {h : ℕ} {(k , v) : Key × V}
              {P : Pred (Key × V) ℓₐ}
              {{@erased l<u : l <⁺ [ k ]}} {{@erased p<u : [ k ] <⁺ u}}
              {m : BOBMap V l u h}
              → P (k , v)
              → All P m
              → All P (proj₂ $ insert (k , v) m)
  allInsert p leaf = node p leaf leaf
  allInsert {h = _} {k , v} p (node {h = _} {(k' , v')} {lt} {rt} {bal = bal} a allL allR) with compare k k'
  ... | le k<k' = alljoinᴸ {lt⁺ = m } a (allInsert ⦃ p<u = [ k<k' ]ᴿ ⦄ p allL) allR bal
    where
      m = insert (k , v) ⦃ p≤u = [ k<k' ]ᴿ ⦄ lt
  ... | eq refl = node p allL allR
  ... | ge k'<k = alljoinᴿ {rt⁺ = m} a allL (allInsert ⦃ [ k'<k ]ᴿ ⦄ p allR) bal
    where
      m = insert (k , v) ⦃ [ k'<k ]ᴿ ⦄ rt

-- -}
-- -}
-- -}
-- -}
-- -}
